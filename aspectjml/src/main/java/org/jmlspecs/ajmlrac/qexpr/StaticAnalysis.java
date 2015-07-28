/* $Id: StaticAnalysis.java,v 1.19 2007/11/04 16:12:11 f_rioux Exp $
 *
 * Copyright (C) 2001, 2002 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 */

package org.jmlspecs.ajmlrac.qexpr;

import java.util.LinkedList;

import org.jmlspecs.ajmlrac.AbstractExpressionTranslator;
import org.jmlspecs.ajmlrac.NotImplementedExpressionException;
import org.jmlspecs.ajmlrac.RacContext;
import org.jmlspecs.ajmlrac.RacNode;
import org.jmlspecs.ajmlrac.RacParser;
import org.jmlspecs.ajmlrac.TransExpression;
import org.jmlspecs.ajmlrac.TransExpression2;
import org.jmlspecs.ajmlrac.TransUtils;
import org.jmlspecs.ajmlrac.VarGenerator;
import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlRelationalExpression;
import org.jmlspecs.checker.JmlSpecExpression;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.jmlspecs.checker.JmlStdType;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JVariableDefinition;

/**
 * An abstract class for translating JML quantified expressions
 * into Java source code. The translation is based on the static
 * analysis of the expression's structures.
 */
abstract class StaticAnalysis extends Translator {
    /**
     * Constructs a <code>StaticAnalysis</code> object.
     *
     * @param varGen    variable generator to be used in translation for
     *                  generating unique local variables.
     * @param expr      quantified expression to be translated.
     * @param resultVar variable name to have the value of quantified
     *                  expression in the translated code.
     * @param transExp  translator to use for translating subexpressions of
     *                  the quantified expression.
     */
    protected StaticAnalysis(/*@ non_null @*/ VarGenerator varGen,
                             /*@ non_null @*/ RacContext ctx,
                 /*@ non_null @*/ JmlSpecQuantifiedExpression expr,
                 /*@ non_null @*/ String resultVar,
			     /*@ non_null @*/ AbstractExpressionTranslator transExp) {
        super(varGen, ctx, expr, resultVar, transExp);
    }

    /**
     * Returns an instance of <code>StaticAnalysis</code>, that
     * translates JML quantified expressions into Java source code.
     *
     * @param varGen    variable generator to be used in translation for
     *                  generating unique local variables.
     * @param expr      quantified expression to be translated.
     * @param resultVar variable name to store the result value of quantified
     *                  expression in the translated code.
     * @param transExp  translator to use for translating subexpressions.
     */
    public static StaticAnalysis getInstance(
    		/*@ non_null @*/ VarGenerator varGen,
    		/*@ non_null @*/ RacContext ctx,
    		/*@ non_null @*/ JmlSpecQuantifiedExpression expr,
    		/*@ non_null @*/ String resultVar,
    		/*@ non_null @*/ AbstractExpressionTranslator transExp) {

        CType type = expr.quantifiedVarDecls()[0].getType();
        if (type.isOrdinal()) {
            return new IntervalBased(varGen, ctx, expr, resultVar, transExp);
        } else if (type.isBoolean()) {
            return new EnumerationBased(varGen, ctx, expr, resultVar, transExp);
        } else {
            return new SetBased(varGen, ctx, expr, resultVar, transExp);
        }
    }

    /**
     * Translate a JML quantified expression into Java source code
     * and return the result.
     *
     * @return translated Java source code.
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    public RacNode translate() throws NonExecutableQuantifierException {
        if (quantiExp.isForAll())
            return translateForAll();
        if (quantiExp.isExists())
            return translateExists();
        if (quantiExp.isSum())
            return translateSum();
        if (quantiExp.isProduct())
            return translateProduct();
        if (quantiExp.isMin())
            return translateMin();
        if (quantiExp.isMax())
            return translateMax();
        if (quantiExp.isNumOf())
            return translateNumOf();

        //@ unreachable;
        throw new NonExecutableQuantifierException();
    }

    public String translateAsString() throws NonExecutableQuantifierException {
        if (quantiExp.isForAll())
            return translateForAllAsString();
        if (quantiExp.isExists())
            return translateExistsAsString();

        //@ unreachable;
        throw new NonExecutableQuantifierException();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of a univeral quantifier.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\forall T x1, ..., xn; P; Q), r]] =
     *     r = true;
     *     Collection c1 = null;
     *     [[S, c1]]  // S is the qset of P ==> Q
     *     Iterator iter1 = c1.iterator();
     *     while (r &amp;&amp; iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[S, cn]]
     *        Iterator itern = cn.iterator();
     *        while (r &amp;&amp; itern.hasNext()) {
     *            T xn = itern.next();
     *            [[P ==&gt; Q, r]]
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\forall T x1, ..., xn; P; Q), r]] =
     *     r = true;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[l1 and u1 calculation from P]]
     *     while (r &amp;&amp; l < u) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[ln and un calculation from P]]
     *        while (r &amp;&amp; ln < un) {
     *            T xn = ln;
     *            [[P ==&gt; Q, r]]
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateForAll() throws NonExecutableQuantifierException {
        return transForAllOrExists();
    }

    private String translateForAllAsString() throws NonExecutableQuantifierException {
        return transForAllOrExistsAsString();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of an existential quantifier.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\exists T x1, ..., xn; P; Q), r]] =
     *     r = false;
     *     Collection c1 = null;
     *     [[S, c1]]  // S is the qset of P ==> Q
     *     Iterator iter1 = c1.iterator();
     *     while (!r &amp;&amp; iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[S, cn]]
     *        Iterator itern = cn.iterator();
     *        while (!r &amp;&amp; itern.hasNext()) {
     *            T xn = itern.next();
     *            [[P &amp;&amp; Q, r]]
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\exists T x1, ..., xn; P; Q), r]] =
     *     r = false;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[l1 and u1 calculation from P]]
     *     while (!r &amp;&amp; l < u) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[ln and un calculation from P]]
     *        while (!r &amp;&amp; ln < un) {
     *            T xn = ln;
     *            [[P &amp;&amp; Q, r]]
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */

    private RacNode translateExists() throws NonExecutableQuantifierException {
        return transForAllOrExists();
    }

    private String translateExistsAsString() throws NonExecutableQuantifierException {
        return transForAllOrExistsAsString();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of a generalized quantifier <code>\sum</code>.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\sum T x1, ..., xn; P; Q), r]] =
     *     r = 0;
     *     Collection c1 = null;
     *     [[S1, c1]]  // S1 is the qset of P for x1
     *     Iterator iter1 = c1.iterator();
     *     while (iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[Sn, cn]] // Sn is the qset of P for xn
     *        Iterator itern = cn.iterator();
     *        while (itern.hasNext()) {
     *            T xn = itern.next();
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = resultVar + v2;
     *            }
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\sum T x1, ..., xn; P; Q), r]] =
     *     r = 0;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[calculation of l1 and u1 from P]]
     *     while (l1 < u1) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[calculation of ln and un from P]]
     *        while (ln < un) {
     *            T xn = ln;
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = resultVar + v2;
     *            }
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateSum() throws NonExecutableQuantifierException {
        return transSumOrProduct();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of a generalized quantifier <code>\product</code>.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\product T x1, ..., xn; P; Q), r]] =
     *     r = 1;
     *     Collection c1 = null;
     *     [[S1, c1]]  // S1 is the qset of P for x1
     *     Iterator iter1 = c1.iterator();
     *     while (iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[Sn, cn]] // Sn is the qset of P for xn
     *        Iterator itern = cn.iterator();
     *        while (itern.hasNext()) {
     *            T xn = itern.next();
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = resultVar * v2;
     *            }
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\product T x1, ..., xn; P; Q), r]] =
     *     r = 0;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[calculation of l1 and u1 from P]]
     *     while (l1 < u1) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[calculation of ln and un from P]]
     *        while (ln < un) {
     *            T xn = ln;
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = resultVar * v2;
     *            }
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateProduct() throws NonExecutableQuantifierException {
        return transSumOrProduct();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of a generalized quantifier <code>\min</code>.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\min T x1, ..., xn; P; Q), r]] =
     *     r = Integer.MAX_VALUE;
     *     Collection c1 = null;
     *     [[S1, c1]]  // S1 is the qset of P for x1
     *     Iterator iter1 = c1.iterator();
     *     while (iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[Sn, cn]] // Sn is the qset of P for xn
     *        Iterator itern = cn.iterator();
     *        while (itern.hasNext()) {
     *            T xn = itern.next();
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = Math.min(resultVar, v2);
     *            }
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\max T x1, ..., xn; P; Q), r]] =
     *     r = Integer.MAX_VALUE;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[calculation of l1 and u1 from P]]
     *     while (l1 < u1) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[calculation of ln and un from P]]
     *        while (ln < un) {
     *            T xn = ln;
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = Math.min(resultVar, v2);
     *            }
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateMin() throws NonExecutableQuantifierException {
        return transMinOrMax();
    }

    /**
     * Return Java source code for evaluating a JML quantified expression
     * of a generalized quantifier <code>\max</code>.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\max T x1, ..., xn; P; Q), r]] =
     *     r = Integer.MIN_VALUE;
     *     Collection c1 = null;
     *     [[S1, c1]]  // S1 is the qset of P for x1
     *     Iterator iter1 = c1.iterator();
     *     while (iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[Sn, cn]] // Sn is the qset of P for xn
     *        Iterator itern = cn.iterator();
     *        while (itern.hasNext()) {
     *            T xn = itern.next();
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = Math.max(resultVar, v2);
     *            }
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\max T x1, ..., xn; P; Q), r]] =
     *     r = Integer.MIN_VALUE;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[calculation of l1 and u1 from P]]
     *     while (l1 < u1) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[calculation of ln and un from P]]
     *        while (ln < un) {
     *            T xn = ln;
     *            boolean v1 = false;
     *            [[P, v1]]
     *            if (v1) {
     *               T_Q v2 = T_init;
     *               [[Q, v2]]
     *               resultVar = Math.max(resultVar, v2);
     *            }
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateMax() throws NonExecutableQuantifierException {
        return transMinOrMax();
    }

    /**
     * Returns code for evaluating numerical quantifiers<code>\num_of</code>.
     * The returned code has the following general form:
     * <p/>
     * <pre>
     *   [[(\num_of T x1, ..., xn; P; Q), r]] =
     *     r = 0;
     *     Collection c1 = null;
     *     [[S1, c1]]  // S1 is the qset of P for x1
     *     Iterator iter1 = c1.iterator();
     *     while (iter1.hasNext()) {
     *        T x1 = iter1.next();
     *        ...
     *        Collection cn = null;
     *        [[Sn, cn]] // Sn is the qset of P for xn
     *        Iterator itern = cn.iterator();
     *        while (itern.hasNext()) {
     *            T xn = itern.next();
     *            boolean v1 = false;
     *            [[P, v1]]
     *            boolean v2 = false;
     *            [[Q, v2]]
     *            if (v1 && v2) {
     *               resultVar++;
     *            }
     *        }
     *        ...
     *     }
     * </pre>
     * <p/>
     * If the type (<code>T</code>) of the quantified variables is
     * <code>byte</code>, <code>char</code>, <code>short</code>,
     * <code>int</code>, or <code>long</code>. The following rule is
     * applied:
     * <p/>
     * <pre>
     *   [[(\num_of T x1, ..., xn; P; Q), r]] =
     *     r = 0;
     *     T l1 = 0;
     *     T u1 = 0;
     *     [[calculation of l1 and u1 from P]]
     *     while (l1 < u1) {
     *        T x1 = l1;
     *        ...
     *        T ln = 0;
     *        T un = 0;
     *        [[calculation of ln and un from P]]
     *        while (ln < un) {
     *            T xn = ln;
     *            boolean v1 = false;
     *            [[P, v1]]
     *            boolean v2 = false;
     *            [[Q, v2]]
     *            if (v1 && v2) {
     *               resultVar++;
     *            }
     *            ln = ln + 1;
     *        }
     *        ...
     *        l1 = l1 + 1;
     *     }
     * </pre>
     *
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    private RacNode translateNumOf() throws NonExecutableQuantifierException {

        // Handle TransExpression2 (FRioux)
        //if(transExp instanceof TransExpression2){
        //	throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Num_of JmlSpecQuantifiedExpression"));
        //}

        RacNode result = null;
        final JmlPredicate pred = quantiExp.predicate();
        {
            // code for evaluating the body:
            //   boolean v1 = false;
            //   [[pred, v1]]
            //   boolean v2 = false;
            //   [[specExp, v1]]
            //   if (v1 && v2) {
            //      resultVar++;
            //   }
            String v1 = varGen.freshVar();
            RacNode c1 = transExpression(pred, v1);
            String v2 = varGen.freshVar();
            RacNode c2 = transExpression(quantiExp.specExpression(), v2);
            result = RacParser.parseStatement(
                    "boolean " + v1 + " = false;\n" +
                            "$0\n" +
                            "if (" + v1 + ") {\n" +
                            "  boolean " + v2 + " = false;\n" +
                            "$1\n" +
                            "  if (" + v2 + ") {\n" +
                            "    " + resultVar + "++;\n" +
                            "  }\n" +
                            "}",
                    c1, c2.incrIndent());
        }

        // code for loop to evaluate quantification
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        for (int i = varDefs.length - 1; i >= 0; i--) {
            result = generateLoop(varDefs[i], rangePredicate(), null, result);
        }

        return RacParser.parseStatement(
                "{ // from num_of expression\n" +
                        "  " + resultVar + " = 0;\n" +
                        "$0\n" +
                        "}",
                result.incrIndent());
    }

    /**
     * Returns Java source code for evaluating the JML quantified
     * expression, which is either a universal or existential
     * quantifier.  Refer to the method <code>translateForAll</code>
     * and <code>translateExists</code> for the structure of the
     * returned code.
     * <p/>
     * <pre><jml>
     * requires quantiExp.isForAll() || quantiExp.isExists();
     * ensures \result != null;
     * </jml></pre>
     *
     * @see #translateForAll()
     * @see #translateExists()
     */
    private RacNode transForAllOrExists()
            throws NonExecutableQuantifierException {
        final boolean isForAll = quantiExp.isForAll();
        final String cond = (isForAll ? "" : "!") + resultVar;
        final String initVal = isForAll ? "true" : "false";

        // build code for evaluating the body, i.e.,
        // P ==> Q for (\forall D; P; Q) and P && Q for (\exists D; P; Q).
        JExpression expr = unwrapJmlExpression(quantiExp.specExpression());
        final JmlPredicate pred = quantiExp.predicate();
        if (pred != null) {
            if (isForAll)
                expr = new JmlRelationalExpression(NO_REF, OPE_IMPLIES,
                        pred, expr);
            else
                expr = new JConditionalAndExpression(NO_REF, pred, expr);
        }
        RacNode result = transExpression(expr, resultVar);

        // build code for while loops to evaluate the body
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        for (int i = varDefs.length - 1; i >= 0; i--) {
            result = generateLoop(varDefs[i], rangePredicate(), cond, result);
        }

        // wrap the resulting code in try statement
        if (transExp instanceof TransExpression) {
            result = RacParser.parseStatement(
                    "try {\n" +
                            "  " + resultVar + " = " + initVal + ";\n" +
                            "$0\n" +
                            "}\n" +
                            "catch (JMLNonExecutableException " + varGen.freshVar() + ") {\n" +
                            "  " + context.angelicValue(resultVar) + ";\n" +
                            "}\n" +
                            "catch (java.lang.Exception " + varGen.freshVar() + ") {\n" +
                            "  " + context.demonicValue(resultVar) + ";\n" +
                            "}",
                    result.incrIndent());
        }
        return result;
    }

    private String transForAllOrExistsAsString()
            throws NonExecutableQuantifierException {
        final StringBuffer code = new StringBuffer();
        final boolean isForAll = quantiExp.isForAll();
        final String cond = (isForAll ? "" : "!") + resultVar;

        // build code for evaluating the body, i.e.,
        // P ==> Q for (\forall D; P; Q) and P && Q for (\exists D; P; Q).
        JExpression expr = unwrapJmlExpression(quantiExp.specExpression());
        final JmlPredicate pred = quantiExp.predicate();
        if (pred != null) {
            if (isForAll)
                expr = new JmlRelationalExpression(NO_REF, OPE_IMPLIES,
                        pred, expr);
            else
                expr = new JConditionalAndExpression(NO_REF, pred, expr);
        }
//    	RacNode result = transExpression(expr, resultVar);
        String resultStr = transExpressionAsString(expr, resultVar);
        String preQCode = AspectUtil.getInstance().getQuantifierInnerClassesForTrans(resultStr);

        resultStr = "       " + resultStr;
//    	code.append(resultStr);
        // build code for while loops to evaluate the body
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        String preWhile = "";
        String resultingWhile = "";
        for (int i = varDefs.length - 1; i >= 0; i--) {
//    		result = generateLoop(varDefs[i], rangePredicate(), cond, result);
            resultingWhile = generateLoopAsString(varDefs[i], rangePredicate(), cond, null);
            if (!preWhile.equals("")) {
                resultingWhile = resultingWhile.replace("$1", preWhile);
            }
            preWhile = generateLoopAsString(varDefs[i], rangePredicate(), cond, null);
        }
        code.append(resultingWhile.replace("$1", preQCode + resultStr));
        // wrap the resulting code in try statement
        return code.toString();
    }

    /**
     * Returns the range predicate of the quantified expression. The
     * result is the conjuntion of explicit and implicit range
     * predicates. The implicit range (e.g., p in (\forall d; r; p ==>
     * q) and (\exists d; r; p && q)) is extracted from the predicate
     * part of the quantified expressions and conjoined to the
     * explicit range predicate (r).
     * <p/>
     * <pre><jml>
     * requires quantiExp.isForAll() || quantiExp.isExists();
     * ensures (* \result maybe null *);
     * </jml></pre>
     *
     * @see #transForAllOrExists()
     */
    private JExpression rangePredicate() {
        // extract the explicit range predicate
        JExpression erange = unwrapJmlExpression(quantiExp.predicate());

        // calculate the implicit range predicate, i.e.,
        // p in p ==> q for \forall and p in p && q for \exists.
        JExpression irange = null;
        JExpression expr = unwrapJmlExpression(quantiExp.specExpression());
        if (quantiExp.isForAll() &&
                (expr instanceof JmlRelationalExpression) &&
                ((JmlRelationalExpression) expr).isImplication()) {
            irange = ((JmlRelationalExpression) expr).left();
        } else if ((quantiExp.isExists() || quantiExp.isNumOf()) &&
                (expr instanceof JConditionalAndExpression)) {
            irange = ((JConditionalAndExpression) expr).left();
        }

        // combine explicit and implicit range predicates
        if (erange == null) {
            return irange;
        }
        if (irange == null) {
            return erange;
        }
        return new JConditionalAndExpression(NO_REF, erange, irange);
    }

    /**
     * Unwraps a given JML expression if it is an instance of
     * JmlPredicate or JmlSpecExpression.
     */
    private static JExpression unwrapJmlExpression(JExpression expr) {
        if (expr instanceof JmlPredicate) {
            return unwrapJmlExpression(((JmlPredicate) expr).specExpression());
        }
        if (expr instanceof JmlSpecExpression) {
            return unwrapJmlExpression(((JmlSpecExpression) expr).expression());
        }
        return expr;
    }

    /**
     * Returns Java source code for evaluating the JML quantified
     * expression, which is a generalized quantifier <code>\sum</code>
     * or <code>\product</code>.
     * <p/>
     * <pre><jml>
     * requires quantiExp.isSum() || quantiExp.isProduct();
     * </jml></pre>
     *
     * @see #translateProduct()
     * @see #translateSum()
     */
    private RacNode transSumOrProduct() throws NonExecutableQuantifierException {

        // Handle TransExpression2 (FRioux)
        if (transExp instanceof TransExpression2) {
            throw (new NotImplementedExpressionException(quantiExp.getTokenReference(), "Sum or Product JmlSpecQuantifiedExpression"));
        }

        final boolean isSum = quantiExp.isSum();
        final String sumOpr = isSum ? " + " : " * ";
        final String initVal = isSum ? "0" : "1";
        final String initBigintVal = isSum ? "java.math.BigInteger.ZERO" : "java.math.BigInteger.ONE";

        RacNode result = null;
        final JmlPredicate pred = quantiExp.predicate();
        final JmlSpecExpression specExpr = quantiExp.specExpression();
        {
            // code for evaluating the body:
            //   boolean v1 = false;
            //   [[pred, v1]]
            //   if (v1) {
            //      T v2 = T_init;
            //      [[specExpr, v2]]
            //      resultVar = resultVar [+ | *] v2;
            //   }
            String v1 = varGen.freshVar();
            RacNode c1 = transExpression(pred, v1);
            String v2 = varGen.freshVar();
            RacNode c2 = transExpression(specExpr, v2);
            result = RacParser.parseStatement(
                    "boolean " + v1 + " = false;\n" +
                            "$0\n" +
                            "if (" + v1 + ") {\n" +
                            "  " + TransUtils.toString(specExpr.getType()) + " " + v2 + (specExpr.getType() == JmlStdType.Bigint ? " = java.math.BigInteger.ZERO;\n" : " = 0;\n") +
                            "$1\n" +
                            "  " + resultVar + " = " + applySumOrProduct(resultVar, sumOpr, v2, specExpr.getType()) + ";\n" +
                            "}",
                    c1, c2.incrIndent());
        }

        // code for while loops to evaluate quantification
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        for (int i = varDefs.length - 1; i >= 0; i--) {
            result = generateLoop(varDefs[i], pred, null, result);
        }

        return RacParser.parseStatement(
                "{ // from " + (isSum ? "sum" : "product") + " expression\n" +
                        "  " + resultVar + " = " + (specExpr.getType() == JmlStdType.Bigint ? initBigintVal : initVal) + ";\n" +
                        "$0\n" +
                        "}",
                result.incrIndent());
    }

    /*
    * returns a string of java code which represents the code "resultVar [+ | *] v2"
    * in transSumOrProduct() for <code>\sum</code> and <code>\product</code>. It's
    * mainly used to support the type \bigint.
    * @param vType the type of strResultVar and v2.
    * @see #transSumOrProduct()
    */
    private String applySumOrProduct(String strResultVar, String strOptr, String strV2, CType vType) {
        String strRet;

        if (vType == JmlStdType.Bigint) {
            if (strOptr.indexOf("*") >= 0) {
                strRet = strResultVar + ".multiply(" + strV2 + ")";
            } else {
                strRet = strResultVar + ".add(" + strV2 + ")";
            }
        } else {
            strRet = strResultVar + strOptr + strV2;
        }

        return strRet;
    }

    /**
     * Returns Java source code for evaluating the JML quantified
     * expression, which is a generalized quantifier <code>\min</code>
     * or <code>\max</code>.
     * <p/>
     * <pre><jml>
     * requires quantiExp.isMin() || quantiExp.isMax();
     * </jml></pre>
     *
     * @see #translateMax()
     * @see #translateMin()
     */
    private RacNode transMinOrMax() throws NonExecutableQuantifierException {

        // Handle TransExpression2 (FRioux)
        //if(transExp instanceof TransExpression2){
        //	throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Min or Max JmlSpecQuantifiedExpression"));
        //}

        final boolean isMin = quantiExp.isMin();
        final String mathMeth = isMin ? "min" : "max";
        final JmlSpecExpression specExpr = quantiExp.specExpression();

        RacNode result = null;
        final JmlPredicate pred = quantiExp.predicate();
        {
            // code for evaluating the body:
            //   boolean v1 = false;
            //   [[pred, v1]]
            //   if (v1) {
            //      T v2 = T_init;
            //      [[specExpr, v2]]
            //      resultVar = Math.min(x, resultVar);
            //   }
            String v1 = varGen.freshVar();
            RacNode c1 = transExpression(pred, v1);
            String v2 = varGen.freshVar();
            RacNode c2 = transExpression(specExpr, v2);

            String neededCast = "";
            if (transExp instanceof TransExpression2) {
                neededCast = "(" + specExpr.getType().toString() + ") ";
            }

            result = RacParser.parseStatement(
                    "boolean " + v1 + " = false;\n" +
                            "$0\n" +
                            "if (" + v1 + ") {\n" +
                            "  " + TransUtils.toString(specExpr.getType()) + " " + v2 + (specExpr.getType() == JmlStdType.Bigint ? " = java.math.BigInteger.ZERO;\n" : " = 0;\n") +

                            "$1\n" +
                            "  if(bFirstCompare) {\n" +
                            "  " + resultVar + " = " + v2 + ";\n" +
                            "  } else {\n" +
                            "  " + resultVar + " = " + (specExpr.getType() == JmlStdType.Bigint ? resultVar + "." + mathMeth + "(" + v2 + ")" :
                            neededCast + "java.lang.Math." + mathMeth + "(" + resultVar + ", " + v2 + ")") + ";\n" +
                            "  }\n" +
                            "  bFirstCompare = false;\n" +
                            "}",
                    c1, c2.incrIndent());
        }

        // code for the while loop
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        for (int i = varDefs.length - 1; i >= 0; i--) {
            result = generateLoop(varDefs[i], pred, null, result);
        }

        return RacParser.parseStatement(
                "{ // from " + (isMin ? "min" : "max") + " expression\n" +
                        "  boolean bFirstCompare = true;\n" +
                        "$0\n" +
                        "}",
                result.incrIndent());
    }

    /**
     * Returns a loop code that evaluates the given body with the
     * quantified variable bound to each possible value of the range.
     * For example, the interval-based approach returns the following
     * form of code:
     * <p/>
     * <pre>
     *  {
     *    T l = 0;
     *    T u = 0;
     *    [[eval of l and u from predicate part]]
     *    while (l < u) {
     *      T x = l;
     *      result
     *      l = l + 1;
     *    }
     *  }
     * </pre>
     * where <code>x</code> is the quantified variable.
     *
     * @param body code to be executed as the loop body
     * @throws NonExecutableQuantifierException if not executable.
     */
    public RacNode generateLoop(RacNode body)
            throws NonExecutableQuantifierException {
        RacNode result = body;

        JExpression pred = null; // range predicate
        if (quantiExp.isForAll() || quantiExp.isExists()) {
            // take into account of implicit range predicates
            pred = rangePredicate();
        } else {
            pred = unwrapJmlExpression(quantiExp.predicate());
        }
        JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
        for (int i = varDefs.length - 1; i >= 0; i--) {
            result = generateLoop(varDefs[i], pred, null, result);
        }

        return RacParser.parseStatement(
                "{ // from quantified expression\n" +
                        "$0\n" +
                        "}",
                result.incrIndent());
    }

    /**
     * Returns a loop code evaluating the body of the quantified predicate.
     *
     * @param varDef quantified variable
     * @param qexpr  target expression for interval calculation (i.e.,
     *               normally, the predicate part of the quantified
     *               expression)
     * @param cond   additional condition to be conjoined (&amp;&amp;)
     *               to the loop condition; <code>null</code> for no
     *               conjoinable condition.
     * @param result code for evaluating expression part (or inner loop)
     * @throws <code>NonExecutableQuantifierException</code> if not executable.
     */
    protected abstract RacNode generateLoop(
	/*@ non_null @*/ JVariableDefinition varDef,
    JExpression qexpr,
    String cond,
	/*@ non_null @*/ RacNode result)
            throws NonExecutableQuantifierException;

    protected abstract String generateLoopAsString(
    		/*@ non_null @*/ JVariableDefinition varDef,
            JExpression qexpr,
            String cond,
    		/*@ non_null @*/ RacNode result)
            throws NonExecutableQuantifierException;

    /**
     * A concrete class for translating JML quantified expressions
     * into Java source code. The translation is based on the
     * set-based static analysis of the expression's structures.
     */
    private static class SetBased extends StaticAnalysis {

        /**
         * Constructs a <code>SetBased</code> object.
         *
         * @param varGen    variable generator to be used in translation for
         *                  generating unique local variables.
         * @param expr      quantified expression to be translated.
         * @param resultVar variable name to have the value of quantified
         *                  expression in the translated code.
         * @param transExp  translator to use for translating subexpressions of
         *                  the quantified expression.
         */
        private SetBased(/*@ non_null @*/ VarGenerator varGen,
                         /*@ non_null @*/ RacContext ctx,
			 /*@ non_null @*/ JmlSpecQuantifiedExpression expr,
			 /*@ non_null @*/ String resultVar,
			 /*@ non_null @*/ AbstractExpressionTranslator transExp) {
            super(varGen, ctx, expr, resultVar, transExp);
        }

        /**
         * Returns Java source code for evaluating quantified expressions
         * using the QSet-based translation.
         * The returned code has the following general form:
         * <p/>
         * <pre>
         *  java.util.Collection c = new java.util.HashSet();
         *  [[eval of c from qexpr]]
         *  java.util.Iterator iter = c.iterator();
         *  while ([condr &&] c.hasNext()) {
         *    T x = iter.next();
         *    result
         *  }
         * </pre>
         * <p/>
         * where <code>x</code> is the quantified variable of
         * type <code>T</code>.
         *
         * @param varDef quantified variable
         * @param qexpr  target expression for interval calculation (i.e.,
         *               normally, the predicate part of the quantified
         *               expression)
         * @param cond   additional condition to be conjoined (&amp;&amp;)
         *               to the loop condition; <code>null</code> for no extra
         *               condition.
         * @param result code for evaluating expression part (or inner loop)
         * @throws NonExecutableQuantifierException if not executable.
         */
        protected RacNode generateLoop(
			/*@ non_null @*/ JVariableDefinition varDef,
            JExpression qexpr,
            String cond,
			/*@ non_null @*/ RacNode result)
                throws NonExecutableQuantifierException {

            String type = TransUtils.toString(varDef.getType());
            String ident = varDef.ident();
            String cvar = varGen.freshVar();
            String ivar = varGen.freshVar();

            QSet qset = QSet.build(qexpr, ident);
            RacNode qcode = qset.translate(varGen, cvar, transExp);

            StringBuffer code = new StringBuffer();
            code.append("java.util.Collection " + cvar +
                    " = new java.util.HashSet();\n");
            code.append("$0\n");
            code.append("java.util.Iterator " + ivar +
                    " = " + cvar + ".iterator();\n");

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append(String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append(cond + " = true;\n");
                }
            }

            code.append("while ("); // while ([cond &&] ivar.hasNext) ...
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            code.append(ivar + ".hasNext()) {\n");
            code.append("  " + type + " " + ident + " = (" + type + ")" +
                    ivar + ".next();\n");
            code.append("$1\n");
            code.append("}");

            result.incrIndent();

            return RacParser.parseStatement(code.toString(), qcode, result);
        }

        @Override
        protected String generateLoopAsString(JVariableDefinition varDef,
                                              JExpression qexpr, String cond, RacNode result)
                throws NonExecutableQuantifierException {
            String type = TransUtils.toString(varDef.getType());
            String ident = varDef.ident();
            String cvar = varGen.freshVar();
            String ivar = varGen.freshVar();

            QSet qset = QSet.build(qexpr, ident);
            String qcode = qset.translateAsString(varGen, cvar, transExp);

            StringBuffer code = new StringBuffer();
            code.append("       java.util.Collection " + cvar +
                    " = new java.util.HashSet();\n");
//		code.append("$0\n");
            if (qcode != null) {
                code.append(qcode);
            }
            code.append("       java.util.Iterator " + ivar +
                    " = " + cvar + ".iterator();\n");

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append("       " + String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append("       " + cond + " = true;\n");
                }
            }

            code.append("       while ("); // while ([cond &&] ivar.hasNext) ...
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            code.append(ivar + ".hasNext()) {\n");
            code.append("       " + type + " " + ident + " = (" + type + ")" +
                    ivar + ".next();\n");
            code.append("$1\n");
            code.append("       }");

//		result.incrIndent();

            return code.toString();
        }
    }

    /**
     * A concrete class for translating JML quantified expressions
     * into Java source code. The translation is based on the
     * interval-based static analysis of the expression's structures.
     * <p/>
     * <pre><jml>
     * invariant quantiExp.quantifiedVarDecls()[0].getType().isOrdinal();
     * </jml></pre>
     */
    private static class IntervalBased extends StaticAnalysis {

        /**
         * Constructs a <code>IntervalBased</code> object.
         *
         * @param varGen    variable generator to be used in translation for
         *                  generating unique local variables.
         * @param expr      quantified expression to be translated.
         * @param resultVar variable name to have the value of quantified
         *                  expression in the translated code.
         * @param transExp  translator to use for translating subexpressions of
         *                  the quantified expression.
         *                  <pre><jml>
         *                                   requires expr.quantifiedVarDecls()[0].getType().isOrdinal();
         *                                   </jml></pre>
         */
        private IntervalBased(/*@ non_null @*/ VarGenerator varGen,
                              /*@ non_null @*/ RacContext ctx,
			  /*@ non_null @*/ JmlSpecQuantifiedExpression expr,
			  /*@ non_null @*/ String resultVar,
			  /*@ non_null @*/ AbstractExpressionTranslator transExp) {
            super(varGen, ctx, expr, resultVar, transExp);
        }

        /**
         * Returns a loop code for evaluating quantified expressions using
         * the interval-based analysis. The returned code has the following
         * general form:
         * <p/>
         * <pre>
         *  T l = 0;
         *  T u = 0;
         *  [[eval of l and u from pred]]
         *  while ([cond &&] l < u) {
         *    T x = l;
         *    result
         *    l = l + 1;
         *  }
         * </pre>
         * <p/>
         * where <code>x</code> is the quantified variable of type
         * <code>T</code>.
         *
         * @param varDef quantified variable
         * @param pred   target expression for interval calculation (i.e.,
         *               normally, the predicate part of the quantified
         *               expression)
         * @param cond   additional condition to be conjoined (&amp;&amp;)
         *               to the loop condition; <code>null</code> for no extra
         *               condition.
         * @param result code for evaluating expression part (or inner loop)
         * @throws NonExecutableQuantifierException if not executable.
         *                                          <p/>
         *                                          <pre><jml>
         *                                                                                   also
         *                                                                                     requires varDef.getType().isOrdinal();
         *                                                                                   </jml></pre>
         */
        protected RacNode generateLoop(
			/*@ non_null @*/ JVariableDefinition varDef,
            JExpression pred,
            String cond,
			/*@ non_null @*/ RacNode result)
                throws NonExecutableQuantifierException {

            final String type = TransUtils.toString(varDef.getType());
            final int tid = TransUtils.getTypeID(varDef.getType());
            final String ident = varDef.ident();
            final boolean separateLoopVar =
                    !(tid == TID_LONG || tid == TID_INT || tid == TID_BIGINT);

            // define quantified intervals, if possible.
            QInterval interval = null;
            {
                // In finding the interval for i-th qvar, the defining
                // expressions can't refer to i-th and later qvars
                JVariableDefinition[] vdefs = quantiExp.quantifiedVarDecls();
                LinkedList xvars = new LinkedList();
                for (int i = vdefs.length - 1; i >= 0; i--) {
                    xvars.add(vdefs[i].ident());
                    if (ident == vdefs[i].ident())
                        break;
                }
                interval = new QInterval(pred, ident, xvars,
                        tid == TID_BIGINT ? JmlStdType.Bigint :
                                (tid == TID_LONG ?
                                        CStdType.Long : CStdType.Integer));
            }

            String lvar = separateLoopVar ? varGen.freshVar() : ident;
            String uvar = varGen.freshVar();
            RacNode qcode = interval.translate(varGen, lvar, uvar, transExp);

            // declare lower and upper bound variables
            StringBuffer code = new StringBuffer();
            if (tid == TID_BIGINT) {
                code.append("java.math.BigInteger " + lvar + " = java.math.BigInteger.ZERO;\n");
                code.append("java.math.BigInteger " + uvar + " = java.math.BigInteger.ZERO;\n");
            } else if (tid == TID_LONG) {
                code.append("long " + lvar + " = 0L;\n");
                code.append("long " + uvar + " = 0L;\n");
            } else {
                code.append("int " + lvar + " = 0;\n");
                code.append("int " + uvar + " = 0;\n");
            }

            // place holder for evaluation of interval, i.e., qcode
            code.append("$0\n");

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append(String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append(cond + " = true;\n");
                }
            }

            // start of whole loop: while ([cond &&] l < u) ...
            code.append("while (");
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            if (tid == TID_BIGINT) {
                code.append(lvar + ".compareTo(" + uvar + ") < 0) {\n");
            } else {
                code.append(lvar + " < " + uvar + ") {\n");
            }

            // declare and initialize quantified variable in terms of
            // loop variable, lvar, if necessary.
            if (separateLoopVar)
                code.append("  " + type + " " + ident + " = (" + type + ") " +
                        lvar + ";\n");

            // place holder for code for body, i.e., result
            code.append("$1\n");

            // increments loop variable and ends while statement.
            if (tid == TID_BIGINT) {
                code.append("  " + lvar + " = " + lvar + ".add(java.math.BigInteger.ONE);\n");
            } else {
                code.append("  " + lvar + " = " + lvar + " + 1;\n");
            }
            code.append("}");

            result.incrIndent();
            return RacParser.parseStatement(code.toString(), qcode, result);
        }

        protected String generateLoopAsString(
    		/*@ non_null @*/ JVariableDefinition varDef,
            JExpression pred,
            String cond,
    		/*@ non_null @*/ RacNode result)
                throws NonExecutableQuantifierException {

            final String type = TransUtils.toString(varDef.getType());
            final int tid = TransUtils.getTypeID(varDef.getType());
            final String ident = varDef.ident();
            final boolean separateLoopVar =
                    !(tid == TID_LONG || tid == TID_INT || tid == TID_BIGINT);

            // define quantified intervals, if possible.
            QInterval interval = null;
            {
                // In finding the interval for i-th qvar, the defining
                // expressions can't refer to i-th and later qvars
                JVariableDefinition[] vdefs = quantiExp.quantifiedVarDecls();
                LinkedList xvars = new LinkedList();
                for (int i = vdefs.length - 1; i >= 0; i--) {
                    xvars.add(vdefs[i].ident());
                    if (ident == vdefs[i].ident())
                        break;
                }
                interval = new QInterval(pred, ident, xvars,
                        tid == TID_BIGINT ? JmlStdType.Bigint :
                                (tid == TID_LONG ?
                                        CStdType.Long : CStdType.Integer));
            }

            String lvar = separateLoopVar ? varGen.freshVar() : ident;
            String uvar = varGen.freshVar();
            String qcode = interval.translateAsString(varGen, lvar, uvar, transExp);

            // declare lower and upper bound variables
            StringBuffer code = new StringBuffer();
            if (tid == TID_BIGINT) {
                code.append("       java.math.BigInteger " + lvar + " = java.math.BigInteger.ZERO;\n");
                code.append("       java.math.BigInteger " + uvar + " = java.math.BigInteger.ZERO;\n");
            } else if (tid == TID_LONG) {
                code.append("       long " + lvar + " = 0L;\n");
                code.append("       long " + uvar + " = 0L;\n");
            } else {
                code.append("       int " + lvar + " = 0;\n");
                code.append("       int " + uvar + " = 0;\n");
            }

            // place holder for evaluation of interval, i.e., qcode
//    	code.append("$0\n");
            if (qcode != null) {
                code.append(qcode);
            }

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append("       " + String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append("       " + cond + " = true;\n");
                }
            }

            // start of whole loop: while ([cond &&] l < u) ...
            code.append("       while (");
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            if (tid == TID_BIGINT) {
                code.append(lvar + ".compareTo(" + uvar + ") < 0) {\n");
            } else {
                code.append(lvar + " < " + uvar + ") {\n");
            }

            // declare and initialize quantified variable in terms of
            // loop variable, lvar, if necessary.
            if (separateLoopVar)
                code.append("       " + type + " " + ident + " = (" + type + ") " +
                        lvar + ";\n");

            // place holder for code for body, i.e., result
            code.append("$1\n");

            // increments loop variable and ends while statement.
            if (tid == TID_BIGINT) {
                code.append("         " + lvar + " = " + lvar + ".add(java.math.BigInteger.ONE);\n");
            } else {
                code.append("         " + lvar + " = " + lvar + " + 1;\n");
            }
            code.append("       }");

//    	result.incrIndent();
            return code.toString();
        }
    }

    /**
     * A concrete class for translating JML quantified expressions
     * into Java source code. The translation is based on an explicit
     * enumeration of all possible values for the quantified variable.
     * A quantified variable of <code>boolean</code> is implemented in
     * this way.
     * <p/>
     * <pre><jml>
     *  protected invariant quantiExp.quantifiedVarDecls()[0].getType()
     *    == JmlStdType.Boolean;
     * </jml></pre>
     */
    private static class EnumerationBased extends StaticAnalysis {

        /**
         * Constructs a <code>EnumerationBased</code> object.
         *
         * @param varGen    variable generator to be used in translation for
         *                  generating unique local variables.
         * @param expr      quantified expression to be translated.
         * @param resultVar variable name to have the value of quantified
         *                  expression in the translated code.
         * @param transExp  translator to use for translating subexpressions of
         *                  the quantified expression.
         *                  <pre><jml>
         *                                   requires expr.quantifiedVarDecls()[0].getType() ==
         *                                     JmlStdType.Boolean;
         *                                   </jml></pre>
         */
        private EnumerationBased(/*@ non_null @*/ VarGenerator varGen,
                         /*@ non_null @*/ RacContext ctx,
			 /*@ non_null @*/ JmlSpecQuantifiedExpression expr,
			 /*@ non_null @*/ String resultVar,
			 /*@ non_null @*/ AbstractExpressionTranslator transExp) {
            super(varGen, ctx, expr, resultVar, transExp);
        }

        /**
         * Returns Java source code for evaluating quantified expressions
         * using the QSet-based translation.
         * The returned code has the following general form:
         * <p/>
         * <pre>
         *  boolean[] v = { false, true };
         *  for (int i = 0; [cond &&] i < v.length; i++) {
         *    bool x = v[i];
         *    result
         *  }
         * </pre>
         * <p/>
         * where <code>x</code> is the quantified variable and
         * <code>v</code> and <code>i</code> are fresh variables.
         *
         * @param varDef quantified variable
         * @param qexpr  target expression for interval calculation (i.e.,
         *               normally, the predicate part of the quantified
         *               expression)
         * @param cond   additional condition to be conjoined (&amp;&amp;)
         *               to the loop condition; <code>null</code> for no extra
         *               condition.
         * @param result code for evaluating expression part (or inner loop)
         * @throws NonExecutableQuantifierException if not executable.
         */
        protected RacNode generateLoop(
			/*@ non_null @*/ JVariableDefinition varDef,
            JExpression qexpr,
            String cond,
			/*@ non_null @*/ RacNode result)
                throws NonExecutableQuantifierException {

            String ident = varDef.ident();
            String cvar = varGen.freshVar();
            String ivar = varGen.freshVar();
            StringBuffer code = new StringBuffer();
            code.append("boolean[] " + cvar + " = { false, true };\n");

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append(String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append(cond + " = true;\n");
                }
            }

            code.append("for (int " + ivar + " = 0; ");
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            code.append(ivar + " < " + cvar + ".length; ");
            code.append(ivar + "++) {\n");
            code.append("  boolean " + ident + " = " + cvar + "[" + ivar + "];\n");
            code.append("$0\n");
            code.append("}");

            result.incrIndent();
            return RacParser.parseStatement(code.toString(), result);
        }

        @Override
        protected String generateLoopAsString(JVariableDefinition varDef,
                                              JExpression qexpr, String cond, RacNode result)
                throws NonExecutableQuantifierException {
            String ident = varDef.ident();
            String cvar = varGen.freshVar();
            String ivar = varGen.freshVar();
            StringBuffer code = new StringBuffer();
            code.append("boolean[] " + cvar + " = { false, true };\n");

            // FRioux - Handle TransExpression2 by initially setting the condition to true
            if (transExp instanceof TransExpression2 && !(cond == null || cond.equals(""))) {
                char[] condition = cond.toCharArray();
                if (condition[0] == '!') {
                    code.append(String.copyValueOf(condition, 1, cond.length() - 1) + " = false;\n");
                } else {
                    code.append(cond + " = true;\n");
                }
            }

            code.append("for (int " + ivar + " = 0; ");
            if (!(cond == null || cond.equals("")))
                code.append(cond + " && ");
            code.append(ivar + " < " + cvar + ".length; ");
            code.append(ivar + "++) {\n");
            code.append("  boolean " + ident + " = " + cvar + "[" + ivar + "];\n");
            code.append("$0\n");
            code.append("}");

//		result.incrIndent();
            return code.toString();
        }
    }
}
