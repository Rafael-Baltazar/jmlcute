/*
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
 *
 * $Id: QInterval.java,v 1.11 2005/12/09 19:46:03 f_rioux Exp $
 */

package org.jmlspecs.ajmlrac.qexpr;

import org.jmlspecs.ajmlrac.*;
import org.jmlspecs.checker.*;
import org.multijava.mjc.*;
import java.util.*;

/**
 * A class for static approximations of the intervals for quantified
 * variables of integeral types. For example, the static approximation of
 * the interval for a quantified variable <code>x</code> with respect to
 * an expression <code>x &lt;= 0 &amp;&amp; x &gt;= 10</code> is 
 * the interval between <code>0</code> and <code>10</code> including
 * both ends.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.11 $
 */

class QInterval implements RacConstants {

    /**
     * Construct a <code>QInterval</code> object representing the quantifed
     * interval for a (quantified) variable <code>var</code> with respect
     * to the expression <code>expr</code>. 
     * The variables in <code>xvars</code> can't appear in the expressions
     * defining the interval for <code>var</code>.
     *
     * <pre><jml>
     *  requires xvars.contains(var);
     * </jml></pre>
     */
    public QInterval(JExpression expr, /*@ non_null @*/ String var,
		     /*@ non_null @*/ Collection xvars,
                     /*@ non_null @*/ CType type) 
    {
	lower = new LinkedList();
	upper = new LinkedList();
	this.var = var;
	this.xvars = xvars;
        this.type = type;
	calculate(expr);
    }

    /** Calculate the quantified interval with respect to the given 
     * expression.
     * 
     * <pre><jml>
     *  modifies lower, upper;
     * </jml></pre>
     */
    private void calculate(JExpression expr) 
    {
	// unwrap JML expressions such as predicate and spec-expression
	if (expr instanceof JmlPredicate) {
	    expr = ((JmlPredicate)expr).specExpression();
	}
	if (expr instanceof JmlSpecExpression) {
	    expr = ((JmlSpecExpression)expr).expression();
	}

	// is a logical AND (&&) expression?
	if (expr instanceof JConditionalAndExpression) {
	    JConditionalAndExpression bexpr = (JConditionalAndExpression) expr;
	    calculate(bexpr.left());
	    calculate(bexpr.right());
	}

	// is a relational expression?
	if (expr instanceof JRelationalExpression) {
	    JRelationalExpression rexpr = (JRelationalExpression) expr;
	    int oper = rexpr.oper();
	    JExpression left = rexpr.left();
	    JExpression right = rexpr.right();
	    Bound pair = null;

	    // check for recursion, e.g., x < x + 1.
	    CheckRecursion check = new CheckRecursion();
	    if (isLocalVariable(left, var) 
		&& !check.isRecursive(right, xvars)) {
		pair = Bound.fromRightExpression(oper, right, type);
	    } else if (isLocalVariable(right, var)
		&& !check.isRecursive(left, xvars)) {
		pair = Bound.fromLeftExpression(oper, left, type);
	    }

	    // add the pair to lower or upper bound. The class Bound assumes
	    // that the variable is on the right-hand side, e.g., 10 < x.
	    if (pair != null) {
		switch (pair.oper) {
		case OPE_LT:
		case OPE_LE:
		    lower.add(pair);
		    break;
		case OPE_GT:
		case OPE_GE:
		    upper.add(pair);
		    break;
		default:
                    //@ unreachable;
		    throw new RuntimeException("Unreachable reached!");
		}
	    } 
	}
    } // calculate

    /** 
     * Is the expression <code>expr</code> a local variable expression
     * consisting of variable named <code>var</code>? 
     */
    private static boolean isLocalVariable(JExpression expr, String var) 
    {
	if (expr instanceof JUnaryPromote) { // !FIXME! covers all?
	    expr = ((JUnaryPromote)expr).expr();
	}
	return (expr instanceof JLocalVariableExpression) &&
	    ((JLocalVariableExpression)expr).ident().equals(var);
    }

    /**
     * Returns code that evaluates the given lower bound.
     * The returned code has the following form:
     *
     * <pre>
     *  [T tvar = 0;]
     *  [[bound.expr, tvar]]
     *  [var = (T_of_var) tvar;]
     *  var = var + 1; // if bound.oper is <
     * </pre>
     */
    private RacNode transLBound(/*@ non_null @*/ VarGenerator varGen,
                               /*@ non_null @*/ String var,
                               /*@ non_null @*/ AbstractExpressionTranslator transExpr, 
                               /*@ non_null @*/ Bound bound) {
        return transBound(varGen, var, transExpr, bound, OPE_LT);
    }
    
    private String transLBoundAsString(/*@ non_null @*/ VarGenerator varGen,
            /*@ non_null @*/ String var,
            /*@ non_null @*/ AbstractExpressionTranslator transExpr, 
            /*@ non_null @*/ Bound bound) {
     return transBoundAsString(varGen, var, transExpr, bound, OPE_LT);
}

    /**
     * Returns code that evaluates the given upper bound.
     * The returned code has the following form:
     *
     * <pre>
     *  [T tvar = 0;]
     *  [[bound.expr, tvar]]
     *  [var = (T_of_var) tvar;]
     *  var = var + 1; // if bound.oper is >=
     * </pre>
     */
    private RacNode transUBound(/*@ non_null @*/ VarGenerator varGen,
                               /*@ non_null @*/ String var,
                               /*@ non_null @*/ AbstractExpressionTranslator transExpr, 
                               /*@ non_null @*/ Bound bound) {
        return transBound(varGen, var, transExpr, bound, OPE_GE);
    }
    
    private String transUBoundAsString(/*@ non_null @*/ VarGenerator varGen,
            /*@ non_null @*/ String var,
            /*@ non_null @*/ AbstractExpressionTranslator transExpr, 
            /*@ non_null @*/ Bound bound) {
    return transBoundAsString(varGen, var, transExpr, bound, OPE_GE);
}

    /**
     * Returns code that evaluates the given lower or upper bound.
     * The returned code has the following form:
     *
     * <pre>
     *  [T tvar = 0;]
     *  [[bound.expr, tvar]]
     *  [var = (T_of_var) tvar;]
     *  var = var + 1; // if bound.oper is opr
     * </pre>
     */
    private RacNode transBound(/*@ non_null @*/ VarGenerator varGen,
    		/*@ non_null @*/ String var,
    		/*@ non_null @*/ AbstractExpressionTranslator transExp, 
    		/*@ non_null @*/ Bound bound,
    		int opr) {
    	
    	if(transExp instanceof TransExpression){
    		boolean useFreshVar = 
    			!bound.expr.getType().isAlwaysAssignableTo(bound.type);
    		String bvar = useFreshVar ? varGen.freshVar() : var;
    		
    		((TransExpression) transExp).PUT_ARGUMENT(bvar);
    		bound.expr.accept(transExp);
    		RacNode result = (RacNode)((TransExpression) transExp).GET_RESULT();
    		if (useFreshVar) {
    			result = RacParser.parseStatement(
    					// !FIXME!
    					bound.expr.getType().toString()
    					+ " " + bvar + " = " + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							"java.math.BigInteger.ZERO" : "0") + ";\n" +
    							"$0\n" +
    							var + " = (" + bound.type + ") " + bvar + ";",
    							result);
    		}
    		
    		if (bound.oper == opr) {
    			result = RacParser.parseStatement(
    					"$0\n" +
    					var + " = " + var + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							".add(java.math.BigInteger.ONE)" : " + 1") + ";",
    							result);
    		}
    		return result;
    	}
    	
    	// Handle TransExpression2 (FRioux)
    	else if(transExp instanceof TransExpression2){
    		boolean useFreshVar = 
    			!bound.expr.getType().isAlwaysAssignableTo(bound.type);
    		String bvar = useFreshVar ? varGen.freshVar() : var;
    		bound.expr.accept(transExp);
    		String stmt = bvar + " = " + ((TransExpression2) transExp).GET_RESULT() + ";";
    		RacNode result = RacParser.parseStatement(stmt);
    				
    		// (FRioux) Can there be quantified statement to process as in Translator.transExpression() ???  		
    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
	    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
	    	}
    		
    		if (useFreshVar) {
    			result = RacParser.parseStatement(
    					// !FIXME!
    					bound.expr.getType().toString()
    					+ " " + bvar + " = " + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							"java.math.BigInteger.ZERO" : "0") + ";\n" +
    							"$0\n" +
    							var + " = (" + bound.type + ") " + bvar + ";",
    							result);
    		}
    		
    		if (bound.oper == opr) {
    			result = RacParser.parseStatement(
    					"$0\n" +
    					var + " = " + var + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							".add(java.math.BigInteger.ONE)" : " + 1") + ";",
    							result);
    		}
    		return result;
    	}
    	
    	// should never happen
    	return null;
    }
    
    private String transBoundAsString(/*@ non_null @*/ VarGenerator varGen,
    		/*@ non_null @*/ String var,
    		/*@ non_null @*/ AbstractExpressionTranslator transExp, 
    		/*@ non_null @*/ Bound bound,
    		int opr) {
    	StringBuffer code = new StringBuffer("");
    	if(transExp instanceof TransExpression){
    		return "";
    	}
    	
    	// Handle TransExpression2 (FRioux)
    	else if(transExp instanceof TransExpression2){
    		boolean useFreshVar = 
    			!bound.expr.getType().isAlwaysAssignableTo(bound.type);
    		String bvar = useFreshVar ? varGen.freshVar() : var;
    		bound.expr.accept(transExp);
    		String stmt = bvar + " = " + ((TransExpression2) transExp).GET_RESULT() + ";";
    		String result = "       "+stmt;
    		// (FRioux) Can there be quantified statement to process as in Translator.transExpression() ???  		
    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
//    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
	    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
	    	}
    		
    		if (useFreshVar) {
    			String result2 = "       " + 
    					// !FIXME!
    					bound.expr.getType().toString()
    					+ " " + bvar + " = " + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							"java.math.BigInteger.ZERO" : "0") + ";\n" +
    							result + "\n" + "       " +
    							var + " = (" + bound.type + ") " + bvar + ";";
    			code.append(result2);
    		}
    		else{
    			code.append(result);
    		}
    		
    		if (bound.oper == opr) {
    			String result2 =
    					"$0\n" + "       " +
    					var + " = " + var + (bound.expr.getType().getTypeID() == TID_BIGINT ?
    							".add(java.math.BigInteger.ONE)" : " + 1") + ";";
    			code.append(result2);
    		}
    		
    		return code.toString();
    	}
    	
    	// should never happen
    	return null;
    }

    /** 
     * Return Java source code that, if executed, evaluates the quantfied
     * interval, i.e., its lower and upper bound values.
     *
     * @param varGen the variable generator to be used in the translation for
     *               generating unique local variables.
     * @param lowerVar the variable name to refer to the lower bound value
     *                  in the translated code.
     * @param upperVar the variable name to refer to the upper bound value
     *                  in the translated code.
     * @param transExp the translator to use for translating JML expressions.
     * @throws <code>NonExecutableQuantifierException</code> if no interval
     *                                                       is found.
     *
     * The translated code has the following form 
     * (lowerVar &lt;= qvar &lt; upperVar):
     *
     * <pre>
     *  [[l1, lowerVar]]
     *  lowerVar = lowerVar + 1; // if l1.oper is &lt;
     *  T v = 0;
     *  [[li, v]]                // for i=2, ..., n
     *  v = v + 1;               // if li.oper is &lt;
     *  lowerVar = Math.max(lowerVar, v);  
     *  [[u1, upperVar]]
     *  upperVar = upperVar + 1; // if u1.oper is &gt;=
     *  [[ui, v]]                // for i=2, ..., n
     *  v = v + 1;               // if ui.oper is &gt;=
     *  upperVar = Math.min(upperVar, v);  
     * </pre>
     * 
     * where li and ui are lower and upper bounds accumlated.
     */
    public RacNode translate(
        /*@ non_null @*/ VarGenerator varGen,
	/*@ non_null @*/ String lowerVar,
	/*@ non_null @*/ String upperVar,
	/*@ non_null @*/ AbstractExpressionTranslator transExp) 
	throws NonExecutableQuantifierException 
    {
	// no interval found?
	if (lower.size() == 0 || upper.size() == 0) {
	    throw new NonExecutableQuantifierException();
        }

	// to accumulate generated code
	RacNode result = null;

	// code for evaluating the first lower bound, i.e.,
	//  [[l1, lowerVar]]
	//  lowerVar = lowerVar + 1; // iif l1.oper is <
	Iterator iter = lower.iterator();
        result = transLBound(varGen, lowerVar, transExp, (Bound)iter.next());

	// code for evaluating the rest of lower bounds, i.e.,
        //  T v = 0;
	//  [[li, v]]   // for i=2, ..., n
	//  v = v + 1;  // fif li.oper is <
	//  lowerVar = Math.max(lowerVar, v);  
	while (iter.hasNext()) {
	    Bound p = (Bound) iter.next();
	    String v = varGen.freshVar();
            RacNode code = transLBound(varGen, v, transExp, p);
	    result = RacParser.parseStatement(
	        "$0\n" + 
		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
		"$1\n" + 
		lowerVar + " = " + (p.type == JmlStdType.Bigint ? lowerVar + ".max(" + v + ")" : "java.lang.Math.max("+ lowerVar +", "+ v +")") + ";",
		result, code);
	}

	// code for evaluating the first upper bound, i.e.,
	//  [[u1, upperVar]]
	//  upperVar = upperVar + 1; // fif l1.oper is >=
        iter = upper.iterator();
        result = RacParser.parseStatement("$0\n$1", result,
                 transUBound(varGen, upperVar, transExp, (Bound)iter.next()));

	// code for evaluating the rest of upper bounds, i.e.,
	//  [[ui, v]]   // for i=2, ..., n
	//  v++;        // if ui.oper is >=
	//  upperVar = Math.min(upperVar, v);  
	while (iter.hasNext()) {
	    Bound p = (Bound) iter.next();
	    String v = varGen.freshVar();
            RacNode code =  transUBound(varGen, v, transExp, p);
	    result = RacParser.parseStatement(
	        "$0\n" + 
		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
		"$1\n" + 
		upperVar + " = " + (p.type == JmlStdType.Bigint ? upperVar + ".max(" + v + ")" : "java.lang.Math.max("+ upperVar +", "+ v +")") + ";",
		result, code);
	}
	return result;
    }
    
    public String translateAsString(
            /*@ non_null @*/ VarGenerator varGen,
    	/*@ non_null @*/ String lowerVar,
    	/*@ non_null @*/ String upperVar,
    	/*@ non_null @*/ AbstractExpressionTranslator transExp) 
    	throws NonExecutableQuantifierException 
        {
    	
    	// no interval found?
    	if (lower.size() == 0 || upper.size() == 0) {
    	    throw new NonExecutableQuantifierException();
            }

    	// to accumulate generated code
    	RacNode result = null;
    	StringBuffer codeResult = new StringBuffer("");

    	// code for evaluating the first lower bound, i.e.,
    	//  [[l1, lowerVar]]
    	//  lowerVar = lowerVar + 1; // iif l1.oper is <
    	Iterator iter = lower.iterator();
//            result = transLBound(varGen, lowerVar, transExp, (Bound)iter.next());
        String lBound = transLBoundAsString(varGen, lowerVar, transExp, (Bound)iter.next());
      
    	// code for evaluating the rest of lower bounds, i.e.,
            //  T v = 0;
    	//  [[li, v]]   // for i=2, ..., n
    	//  v = v + 1;  // fif li.oper is <
    	//  lowerVar = Math.max(lowerVar, v);  
        if(!iter.hasNext()){
        	codeResult.append(lBound+"\n");
        }
    	while (iter.hasNext()) {
    	    Bound p = (Bound) iter.next();
    	    String v = varGen.freshVar();
//                RacNode code = transLBound(varGen, v, transExp, p);
            String lBound2 = transLBoundAsString(varGen, v, transExp, p);
            codeResult.append(
                		lBound +"\n" + "       " +
    		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
    		lBound2 + "\n" + "       " +
    		lowerVar + " = " + (p.type == JmlStdType.Bigint ? lowerVar + ".max(" + v + ")" : "java.lang.Math.max("+ lowerVar +", "+ v +")") + ";\n");
                
//    	    result = RacParser.parseStatement(
//    	        "$0\n" + 
//    		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
//    		"$1\n" + 
//    		lowerVar + " = " + (p.type == JmlStdType.Bigint ? lowerVar + ".max(" + v + ")" : "java.lang.Math.max("+ lowerVar +", "+ v +")") + ";",
//    		result, code);
    	}

    	// code for evaluating the first upper bound, i.e.,
    	//  [[u1, upperVar]]
    	//  upperVar = upperVar + 1; // fif l1.oper is >=
            iter = upper.iterator();
//            result = RacParser.parseStatement("$0\n$1", result,
//                     transUBound(varGen, upperVar, transExp, (Bound)iter.next()));
            String uBound = transUBoundAsString(varGen, upperVar, transExp, (Bound)iter.next());
         
    	// code for evaluating the rest of upper bounds, i.e.,
    	//  [[ui, v]]   // for i=2, ..., n
    	//  v++;        // if ui.oper is >=
    	//  upperVar = Math.min(upperVar, v);  
            if(!iter.hasNext()){
            	codeResult.append(uBound+"\n");
            }
    	while (iter.hasNext()) {
    	    Bound p = (Bound) iter.next();
    	    String v = varGen.freshVar();
//            RacNode code =  transUBound(varGen, v, transExp, p);
            String uBound2 = transUBoundAsString(varGen, v, transExp, p);
            codeResult.append(uBound+"\n" + "       " +
            		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
            		uBound2+"\n" + "       " +
            		upperVar + " = " + (p.type == JmlStdType.Bigint ? upperVar + ".max(" + v + ")" : "java.lang.Math.max("+ upperVar +", "+ v +")") + ";\n");
            
//    	    result = RacParser.parseStatement(
//    	        "$0\n" + 
//    		TransUtils.toString(p.type) + " " + v + " = " + (p.type == JmlStdType.Bigint ? "java.math.BigInteger.ZERO" : "0") + ";\n" +
//    		"$1\n" + 
//    		upperVar + " = " + (p.type == JmlStdType.Bigint ? upperVar + ".max(" + v + ")" : "java.lang.Math.max("+ upperVar +", "+ v +")") + ";",
//    		result, code);
    	}
    	return codeResult.toString();
        }

    /** a list of <code>Bound</code> objects representing the lower bound.
     *
     * <pre><jml>
     * private invariant (\forall Bound b; lower.contains(b);
     *                      b.oper == OPE_LT || b.oper == OPE_LE);
     * </jml></pre>
     */
    private /*@ non_null @*/ List lower;

    /** a list of <code>Bound</code> objects representing the upper bound.
     *
     * <pre><jml>
     * private invariant (\forall Bound b; upper.contains(b);
     *                      b.oper == OPE_GT || b.oper == OPE_GE);
     * </jml></pre>
     */
    private /*@ non_null @*/ List upper;

    /** the quantified variable name
     *
     * @see #xvars
     */
    private /*@ non_null @*/ String var;

    /** names of excluded variables
     *
     * <pre><jml>
     * private invariant xvars.contains(var);
     * </jml></pre>
     */
    private /*@ non_null @*/ Collection xvars;

    /** The type of the quantified variable. */
    private /*@ non_null @*/ CType type;

    /**
     * A class for representing tuples of <code>JExpression</code> objects
     * and <code>int</code> values. The tuple objects represent lower or
     * upper bounds of quantified intervals. The quantified variable is 
     * assumed to be positioned on the right-hand side; for example, 
     * a bound expression <code>10 &gt; x</code> is represented by a tuple
     * <code>(10,&gt;)</code> and an expression <code>x &gt; 10</code> is 
     * represented by a tuple <code>(10,&lt;)</code>.
     */
    private static class Bound {

	/** 
	 * Returns a bound built from a bound expression with the bound
	 * value, <code>expr</code>, on the left-hand side, e.g., in
	 * <code>10 &gt; x</code>. 
	 *
	 * <pre><jml>
	 *  requires expr != null;
	 * </jml></pre>
	 */
	public static Bound fromLeftExpression(int oper, JExpression expr,
                                               CType type) {
	    return new Bound(oper, expr, type);
	}

	/** 
	 * Returns a bound built from a bound expression with the bound
	 * value, <code>expr</code>, on the right-hand side, e.g., in
	 * <code>x &gt; 10</code>.
	 *
	 * <pre><jml>
	 *  requires expr != null;
	 * </jml></pre> 
	 */
	public static Bound fromRightExpression(int oper, JExpression expr,
                                                CType type) {
	    int opr = oper;
	    switch (opr) {
	    case OPE_LT:
		opr = OPE_GT; break;
	    case OPE_LE:
		opr = OPE_GE; break;
	    case OPE_GT:
		opr = OPE_LT; break;
	    case OPE_GE:
		opr = OPE_LE; break;
	    default:
		throw new RuntimeException("Unreachable reached!");
	    }	    
	    return new Bound(opr, expr, type);
	}

	/** Constructs a <code>Bound</code> object */
	private Bound(int oper, /*@ non_null @*/ JExpression expr, 
                      /*@ non_null @*/ CType type) {
	    this.oper = oper;
	    this.expr = expr;
            this.type = type;
	}
	
	/** bound expression, e.g, <code>10</code> in <code>x &gt; 10</code> */
	public /*@ non_null @*/ JExpression expr;

	/** bound operator, e.g, <code>&gt;</code> in <code>x &gt; 10</code> */
	public int oper;
        
	/** The target type, e.g, <code>x's type</code> in 
         * <code>x &gt; 10</code> */
        public /*@ non_null @*/ CType type;
    }

    /**
     * A class to check an appearance of local variables in an expression.
     */
    private static class CheckRecursion extends AbstractExpressionVisitor {
	public CheckRecursion() {}

	/** Returns <code>true</code> if the expression <code>expr</code>
	 * contains any references to local variables in <code>xvars</code>.
	 */
	public boolean isRecursive(JExpression expr, Collection xvars) {
	    hasRecursion = false;
	    this.xvars = new HashSet();
	    this.xvars.addAll(xvars);
	    expr.accept(this);
	    return hasRecursion;
	}
	public void visitLocalVariableExpression( 
	    JLocalVariableExpression self ) {
	    if (xvars.contains(self.ident())) 
		hasRecursion = true;
	}
	private boolean hasRecursion;
	private Set xvars;
    }
}
