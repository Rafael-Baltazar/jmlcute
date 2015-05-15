/* $Id: TransPostcondition.java,v 1.31 2006/09/12 04:58:29 ye-cui Exp $
 *
 * Copyright (C) 2001 Iowa State University
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

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.*;
import org.jmlspecs.ajmlrac.qexpr.*;
import org.multijava.mjc.*;
import java.util.*;

/**
 * A RAC visitor class for transforming JML postconditions into Java
 * source code. The generated code is a sequence of Java statements
 * that evaluate and store the boolean result in the given variable.
 * The boolean result variable is assumed to be declared in the outer
 * scope that incorporates the code.
 *
 * @see TransExpression
 * @see TransPredicate
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.31 $
 */
public class TransPostcondition extends TransPredicate {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new instance and translates the given
     * postcondition, <code>pred</code>. The translated Java source
     * code can be accessed by such accessor methods as
     * <code>stmt()</code> and <code>wrappedStmt</code>.
     *
     * @param resultVar variable to store the result
     */
     public TransPostcondition( /*@ non_null @*/ VarGenerator varGen,
                                /*@ non_null @*/ RacContext ctx,
				/*@ non_null @*/ VarGenerator oldVarGen,
                                boolean forStatic,
				/*@ non_null @*/ JExpression pred,
				/*@ non_null @*/ String resultVar,
				/*@ non_null @*/ JTypeDeclarationType typeDecl) {
         super(varGen, ctx, pred, resultVar, typeDecl);
	 this.oldVarGen = oldVarGen;
	 oldExprs = new ArrayList();
         this.forStatic = forStatic;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /** Returns a list of old expressions (as <code>RacNode</code>) that
     * must be executed in the pre-state. The declaration of a local 
     * variable to hold the result of the expression is stored in the
     * <code>name</code> field of class <code>RacNode</code>. This method
     * must be called after translation.
     *
     * <pre><jml>
     * normal_behavior
     *  assignable translated;
     *  ensures \result != null && \result == oldExprs;
     * </jml></pre>
     */
    public List oldExprs() {
        perform();
	return oldExprs;
    }

    // ----------------------------------------------------------------------
    // TRANSLATION
    // ----------------------------------------------------------------------

    /**
     * Translates a JML pre expression. The translation 
     * rules for this expression is defined as follows.
     *
     * <pre>
     *   [[\pre(E), r]] = 
     *      r = v;  
     * </pre>
     *
     * with the addition of a field declaration 
     * <code>private T_E v = d_T_E;</code> to the target class, and the 
     * insertion of evaluation <code>[[E, v]]</code> into the method
     * prolog.
     *
     * @see TransOldExpression
     */
    public void visitJmlPreExpression( JmlPreExpression self ) {
	transPreExpression( self );
    }

    /**
     * Translates a JML old expression. The translation 
     * rules for this expression is defined as follows.
     *
     * <pre>
     *   [[\old(E), r]] = 
     *      r = v;  
     * </pre>
     *
     * with the addition of a field declaration 
     * <code>private T_E v = d_T_E;</code> to the target class, and the 
     * insertion of evaluation <code>[[E, v]]</code> into the method
     * prolog.
     *
     * @see TransOldExpression
     */
    public void visitJmlOldExpression( JmlOldExpression self ) {
	transPreExpression( self );
    }

    public void transPreExpression( JmlSpecExpressionWrapper self ) {
        // does the pre expression have any quantified variables?
        if (hasQuantifiedVar(self)) {
            oldExpressionInQuantifiers(self);
            return;
        } 

        // Translates the pre expression such that it is to be
        // evaluated in the pre-state and stores the result into a
        // special private field of type TN_JMLVALUE. The pre
        // expression itself is replaced with a reference to the
        // new private field.

        JExpression expr = self.specExpression();
        CType type = expr.getApparentType();

        // translate the pre expr with a fresh pre-state variable
        String var = oldVarGen.freshVar();
        TransOldExpression tr = 
            new TransOldExpression(oldVarGen, context, expr, var, typeDecl);

        // coerce to type TN_JMLVALUE with appropriate guard against 
        // undefinedness.
        String oldVar = varGen.freshOldVar();
        RacNode node = RacParser.parseStatement(
            "try {\n" +
            "  " + toString(type) + " " + var + " = " + 
                defaultValue(type) + ";\n" +
            "$0\n" +
            "  $1 = " +TN_JMLVALUE+ ".ofObject(" +
                TransUtils.wrapValue(type, var)+ ");\n" +
            "}\n" +
            "catch (JMLNonExecutableException jml$e0) {\n" +
            "  $1 = " +TN_JMLVALUE+ ".ofNonExecutable();\n" +
            "}" +
            "catch (java.lang.Exception jml$e0) {\n" +
            "  $1 = " +TN_JMLVALUE+ ".ofUndefined();\n" +
            "}", 
            tr.stmt().incrIndent(), oldVar);

        // piggy-back the name of new old variable in the name field
        // of the RAC node; the node will be evaluated by the precondition
        // check method.
        node.setVarDecl(PreValueVars.createJmlValueVar(forStatic, oldVar));
        oldExprs.add(node);


        // replace the old expr with a reference to the new old field.
        RacNode stmt = RacParser.parseStatement(
            GET_ARGUMENT() + " = " + 
               TransUtils.unwrapObject(type, oldVar + ".value()") + ";");
        RETURN_RESULT(stmt);

        // add the pre expression to the set of terms to be printed
        // when the assertion is violated.
        java.io.StringWriter writer = new java.io.StringWriter();
        RacPrettyPrinter prt = new RacPrettyPrinter(
            writer, (JmlModifier) Main.modUtil);
	self.accept(prt);
        addDiagTerm(new DiagTerm(escapeString(writer.toString()), oldVar));
    }

    /** Translates the given JML quantified expression. It is overridden
     * here to keep track of the set of quantifiers that enclose the old 
     * expression currently being translated.
     *
     * @see #visitJmlPreExpression(JmlPreExpression)
     * @see #visitJmlOldExpression(JmlOldExpression)
     */
    public void visitJmlSpecQuantifiedExpression( 
       JmlSpecQuantifiedExpression self )
    {
        quantifiers.push(self);
        super.visitJmlSpecQuantifiedExpression(self);
        quantifiers.pop();
    }

    /**
     * Translates a JML result expression. The translation 
     * rules for this expression is defined as follows.
     *
     * <pre>
     *   [[\result, r]] = 
     *     r = VN_RESULT;
     * </pre>
     *
     * with the insertion of a variable declaration 
     * <tt>T VN_RESULT = d_T;</tt> into the method proglog, where 
     * <tt>T</tt> is the return type of the method.
     * The variable <tt>VN_RESULT</tt> is used to capture the return
     * value of the method.
     */
    public void visitJmlResultExpression( JmlResultExpression self ) {
	RacNode stmt = RacParser.parseStatement(
	   GET_ARGUMENT() + " = " + VN_RESULT + ";");
	RETURN_RESULT(stmt);

        // adds "\result" to diagnostic terms, i.e., the set of
        // variables whose values are to be printed if the assertion
        // is violated.
        addDiagTermResult();
    }

    // ----------------------------------------------------------------------
    // HELPER METHODS
    // ----------------------------------------------------------------------

    /** Does the given old or pre expression, <code>expr</code>, have any
     * free quantified variables? */
    private boolean hasQuantifiedVar(JmlSpecExpressionWrapper expr) {
        return new QVarChecker().hasQVar(expr);
    }

    /**
     * Translates a JML old expression, <code>self</code>, enclosed in
     * quantifiers. The translation generates code that evaluates the
     * old expression for each combination of bound variables of
     * quantifiers and stores the result to a private cache. The original
     * old expression is replaced with cache lookup code.
     * 
     * <pre><jml>
     * requires !quantifiers.isEmpty();
     * assignable oldExprs, resultStack;
     * </jml></pre>
     */
    private void oldExpressionInQuantifiers(JmlSpecExpressionWrapper self) {
        JExpression expr = self.specExpression();
        CType type = expr.getApparentType();
        String mapVar = varGen.freshOldVar(); // cache variable
	
        // statements for evaluating old expression, E, of type T.
        //  T v = T_init;
        //  v = [[E]]
        //  mapVar.put(key, v);
        String var = oldVarGen.freshVar();
        String key = buildKey();

        // coerce to type TN_JMLVALUE with appropriate guard against 
        // undefinedness.
        RacNode stmt = 
            new TransOldExpression(oldVarGen,context,expr,var,typeDecl).stmt();
        stmt = RacParser.parseStatement(
            "try {\n" +
            "  " + toString(type) + " " + var + " = " +
                 defaultValue(type) + ";\n" +
            "$0\n" +
            "  " + mapVar + ".put(" + key + ", " +TN_JMLVALUE+ ".ofObject(" +
                 TransUtils.wrapValue(type, var) + "));" +
            "}\n" +
            "catch (JMLNonExecutableException jml$e0) {\n" +
            "  " + mapVar + ".put(" + key + 
                 ", " +TN_JMLVALUE+ ".ofNonExecutable());\n" +
            "}" +
            "catch (java.lang.Exception jml$e0) {\n" +
            "  " + mapVar + ".put(" + key + 
                 ", " +TN_JMLVALUE+ ".ofUndefined());\n" +
            "}", 
            stmt.incrIndent());

        // iteration of the statement over bound variables
        try {
            TransQuantifiedExpression trans = null;
            // As the variable quantifiers is a stack, the translation
            // should be done in the reverse order, i.e., from the
            // inner to outer quantifiers. Thanks to Peter Chan for
            // reporting this error.
            for (int i = quantifiers.size() - 1; i >= 0; i--) {
                trans = new TransQuantifiedExpression(varGen, context,
                            (JmlSpecQuantifiedExpression)quantifiers.get(i), 
                            null, this);
                stmt = trans.generateLoop(stmt);
            }
        } catch (NonExecutableQuantifierException e) {
            
            // contextual interpretation of non-executable expression
            if (context.enabled() && type.isBoolean()) {
                RETURN_RESULT(RacParser.parseStatement(
                   "// from a non_executable, boolean, JML clause\n" +
                   context.angelicValue(GET_ARGUMENT()) +  ";"));
            } else {
                nonExecutableExpression();
            }
            return;
        }

        // piggyback cache declaration in the name field
        stmt.setVarDecl(PreValueVars.createVar(forStatic, 
                                               "JMLOldExpressionCache",
                                               mapVar,
                                               "new JMLOldExpressionCache()"));
        oldExprs.add(stmt);

        // replace the old expr with cache lookup code
        RacNode result = RacParser.parseStatement(
            "if (" + mapVar + ".containsKey(" + key + ")) {\n" +
            "  " + GET_ARGUMENT() + " = " +
               TransUtils.unwrapObject(type, 
                   "((" +TN_JMLVALUE+ ")" +mapVar+ ".get(" +key+ ")).value()") 
               + ";\n" +
            "} else {\n" +
            "  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
            "}");
        RETURN_RESULT(result);        
    }        

    /** Returns a key for retrieving the value of old expression currently
     * being translated. We store the old expression values as a mapping
     * from quantified (bound) variables to values, and the quantified
     * variables beomes a key. For example, if the quantifiers are 
     * <code>x1</code>, <code>x2</code>, ..., <code>xn</code>, the key
     * is <code>new Object[] { x1, x2, ..., xn }</code>, where 
     * <code>xi</code> is wrapped if necessary.
     *
     * <pre><jml>
     * requires !quantifiers.isEmpty();
     * ensures \result != null;
     * </jml></pre>
     */
    private String buildKey() {
        StringBuffer code = new StringBuffer();
        code.append("new java.lang.Object[] { " );
        boolean isFirst = true;
        for (Iterator i = quantifiers.iterator(); i.hasNext(); ) {
            JVariableDefinition[] vars = 
                ((JmlSpecQuantifiedExpression)i.next()).quantifiedVarDecls();
            for (int j = 0; j < vars.length; j++) {
                if (isFirst) {
                    isFirst = false;
                } else {
                    code.append(", ");
                }
                code.append(TransUtils.wrapValue(vars[j].getType(), 
                                                 vars[j].ident()));
            }            
        }
        code.append(" }");
        return code.toString();
    }

    // ----------------------------------------------------------------------
    // INNER CLASS
    // ----------------------------------------------------------------------

    /**
     * A class to check whether an expression has any references to 
     * quantified variables.
     */
    private class QVarChecker extends AbstractExpressionVisitor {
	public QVarChecker() {}

	/** Returns <code>true</code> if the expression <code>expr</code>
	 * contains any references to quantified variables.
	 */
	public boolean hasQVar(JExpression expr) {
	    hasQVar = false;
	    this.qvars = new HashSet();
            for (Iterator i = quantifiers.iterator(); i.hasNext(); ) {
                JVariableDefinition[] vars = 
                  ((JmlSpecQuantifiedExpression)i.next()).quantifiedVarDecls();
                for (int j = 0; j < vars.length; j++) {
                    qvars.add(vars[j].ident());
                }
            }
	    expr.accept(this);
	    return hasQVar;
	}
	public void visitLocalVariableExpression( 
	    JLocalVariableExpression self ) {
	    if (qvars.contains(self.ident())) 
		hasQVar = true;
	}
	private boolean hasQVar;
	private Set qvars;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** Indicates whether this translation is for a static method
     * declaration. */
    private boolean forStatic;

    /** A list of <code>RacNode</code>'s representing old expressions that 
     * must be executed in the pre-state. */
    private /*@ spec_public @*/ List oldExprs;

    /** Variable generator to be used in the translation of old expression. 
     */
    private /*@ non_null @*/ VarGenerator oldVarGen;

    /** The set of quantifiers that enclose the old expression currently
     * being translated.
     * 
     * <pre><jml>
     * private invariant (\forall Object o; quantifiers.contains(o);
     *   o instanceof JmlSpecQuantifiedExpression);
     * </jml></pre>
     */
    private /*@ non_null @*/ Stack quantifiers = new Stack();
}
