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
 * $Id: QSet.java,v 1.11 2005/12/09 19:46:03 f_rioux Exp $
 */

package org.jmlspecs.ajmlrac.qexpr;

import org.jmlspecs.ajmlrac.*;
import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlSpecExpression;
import org.multijava.mjc.*;
import org.multijava.util.compiler.CompilationAbortedError;
import org.multijava.util.compiler.CompilationAbortedException;

/**
 * An abstract class that represetns <em>qset</em>s of quantified
 * expressions. A qset of a quantified expression is a static, 
 * conservative, approximation of the set of all objects that need be 
 * examined to determine the truth of the quantified expression. 
 * To decide the truth of the quantified expression, 
 * each element of the qset is bound and the quantified expression 
 * is evaluated.
 * 
 * The qset classes are organized with the Composite Pattern [GoF95].
 *
 * <pre>
 *  {abstract} QSet
 *  +- Top        ^
 *  +- Leaf       |left, right
 *  +- Composite -+
 *      +- Union
 *      +- Intersection
 * </pre>
 */
abstract class QSet implements RacConstants {
    public static final QSet TOP = new Top();

    /** Returns a new qset built from a JML expression and a quantified
     * variable. */
    public static QSet build(JExpression expr, String var) 
        throws NonExecutableQuantifierException {
	return calculate(expr,var);
    }

    /** Returns a qset representing the union of this and argument. */
    public QSet union(/*@ non_null @*/ QSet s) {
	if (s.isTop())
	    return s;
	return new Union(this, s);
    }

    /** Returns a qset representing the intersection of this and argument. */
    public QSet intersect(/*@ non_null @*/ QSet s) {
	if (s.isTop())
	    return this;
	return new Intersection(this, s);
    }

    /** Is this a special qset <code>TOP</code>? */
    public boolean isTop() {
	return false;
    }

    /** Returns the <em>qset</em> of an expression <code>expr</code> 
     * with respect to the quantified variable <code>var</code>.
     * A qset for a quantified expression is a static, conservative, 
     * approximation of the set of all objects that need be examined 
     * to determine the truth of the quantified expression. To decide
     * the truth of the quantified expression, each element of the qset
     * is bound and the quantified expression is evaluated.
     *
     * @param expr the expression whose qset is being computed.
     * @param var the name of the quantified variable with respect to it
     *            the qset is computed.
     * @return the qset of the expression <code>expr</code> with repect to
     *         the quantified variable <code>var</code>.
     * <pre>
     *  Q[[p && q]] == Q[[p]] intersect Q[[q]]
     *  Q[[p || q]] == Q[[p]] union Q[[q]]
     *  Q[[e.contains(x)]] == 
     *    e   if e is of type Collection and x equals to var.
     *    TOP otherwise
     *  Q[[ ... ]]  == TOP
     * </pre>
     */
    private static QSet calculate(JExpression expr, String var) 
	throws NonExecutableQuantifierException 
    {
	// unwrap if a wrapper expression like JmlExpression.
	// !FIXME! does this cover all?
	if (expr instanceof JmlPredicate) {
	    expr = ((JmlPredicate)expr).specExpression();
	}
	if (expr instanceof JmlSpecExpression) {
	    expr = ((JmlSpecExpression)expr).expression();
	}

	// is a logical and (&&) expression?
	if (expr instanceof JConditionalAndExpression) {
	    JBinaryExpression bexpr = (JBinaryExpression) expr;
	    QSet left = calculate(bexpr.left(), var);
	    QSet right = calculate(bexpr.right(), var);
	    return left.intersect(right);
	}

	// is a logical or (||) expression?
	if (expr instanceof JConditionalOrExpression) {
	    JBinaryExpression bexpr = (JBinaryExpression) expr;
	    QSet left = calculate(bexpr.left(), var);
	    QSet right = calculate(bexpr.right(), var);
	    return left.union(right);
	}

	// is a method call expression?
	if (expr instanceof JMethodCallExpression) {
	    return calculate((JMethodCallExpression)expr, var);
	}

	return TOP;
    }

    /** Returns the <em>qset</em> of a method call expression 
     * <code>expr</code> with respect to the quantified variable 
     * <code>var</code>.
     *
     * @param expr the method call expression whose qset is being computed.
     * @param var the name of the quantified variable with respect to it
     *            the qset is computed.
     * @return the qset of the expression <code>expr</code> with repect to
     *         the quantified variable <code>var</code>.
     * <pre>
     *  Q[[e.contains(x)]] == 
     *    e   if e is of type Collection and x equals to var.
     *    TOP otherwise
     * </pre>
     */
    private static QSet calculate(JMethodCallExpression expr, String var) 
    {
	JExpression prefix = expr.prefix();
	//@ assert prefix != null;
	String ident = expr.ident();
	JExpression[] args = expr.args();

	// is of the correct form, i.e.,  e.contains(x) or e.has(x)?
	if (args == null || args.length != 1 ||
            !("contains".equals(ident) || "has".equals(ident))) 
	    return TOP;
	
	// is the prefix e a subtype of Java or JML collection?
        initCollectionTypes();
	CType type = prefix.getType();
	if (!type.isAlwaysAssignableTo(JAVA_COLLECTION) &&
            !type.isAlwaysAssignableTo(JML_COLLECTION)) {
	    return TOP;
	}

	// does the argument equal to var?
	JExpression arg = args[0];
	// !FIXME! does this cover all?
	if (arg instanceof JUnaryPromote) {
	    arg = ((JUnaryPromote)arg).expr();
	}
	if (arg instanceof JLocalVariableExpression &&
	    var.equals(((JLocalVariableExpression)arg).ident())) {
	    return new Leaf(prefix);
	}

	return TOP;
    }

    /** 
     * Returns Java source code that computes the qset represented by this
     * object.
     *
     * @param varGen the variable generator to be used in the translation for
     *               generating unique local variables.
     * @param resultVar the variable name to refer to the qset object
     *                  in the translated code.
     * @param transExp the translator to use for translating JML expressions.
     */
    public abstract RacNode translate(
        /*@ non_null @*/ VarGenerator varGen,
	/*@ non_null @*/ String resultVar,
	/*@ non_null @*/ AbstractExpressionTranslator transExp) 
	throws NonExecutableQuantifierException; 
    
    public abstract String translateAsString(
            /*@ non_null @*/ VarGenerator varGen,
    	/*@ non_null @*/ String resultVar,
    	/*@ non_null @*/ AbstractExpressionTranslator transExp) 
    	throws NonExecutableQuantifierException; 

    /**
     * A special, concrete qset class that represents the universe of
     * all objects. We use objects of the class <code>Top</code> to denote
     * qsets for JML expressions whose qset can not be statically 
     * determined. In such a situation, all objects of correct type must be
     * examined to determine the truth of the quantified expression.
     * In the implementation, if such a case happens, we throw a
     * NonExecutableQuantifierException.
     * 
     * @see TransQuantifiedExpression
     */
    private static class Top extends QSet {
	private Top() {
	}
	
	/** Return a qset representing the union of this and the argument. */
	public QSet union(/*@ non_null @*/ QSet s) {
	    return this;
	}

	/** Return a qset representing the intersection of this and 
	 * the argument */
	public QSet intersect(/*@ non_null @*/ QSet s) {
	    return s;
	}

	/** Is this a special qset TOP? */
	public boolean isTop() {
	    return true;
	}

	/** 
	 * Return Java source code that computes the qset represented by this
	 * object.
	 *
	 * @param varGen the variable generator to be used in the translation
	 *               for generating unique local variables.
	 * @param resultVar the variable name to refer to the qset object
	 *                  in the translated code.
	 * @param transExp the translator to use for translating JML 
	 *                 expressions.
	 */
	public RacNode translate(
	    /*@ non_null @*/ VarGenerator varGen,
	    /*@ non_null @*/ String resultVar,
	    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
	    throws NonExecutableQuantifierException {
	    throw new NonExecutableQuantifierException();
	}

	@Override
	public String translateAsString(VarGenerator varGen, String resultVar,
			AbstractExpressionTranslator transExp)
			throws NonExecutableQuantifierException {
		// TODO Auto-generated method stub
		 throw new NonExecutableQuantifierException();
	}
    }

    /**
     * A concrete qset class consisting of only one JML expression.
     */
    private static class Leaf extends QSet {
	/** 
	 * Constructs a new <code>Leaf</code> object.
	 *
	 * @param expr JML expression representing qset.
	 */
	private Leaf(/*@ non_null @*/ JExpression expr) {
	    expression = expr;
	}

	/** 
	 * Return Java source code that computes the qset represented by this
	 * object.
	 *
	 * @param varGen the variable generator to be used in the translation
	 *               for generating unique local variables.
	 * @param resultVar the variable name to refer to the qset object
	 *                  in the translated code.
	 * @param transExp the translator to use for translating JML 
	 *                 expressions.
	 */
	public RacNode translate(
	    /*@ non_null @*/ VarGenerator varGen,
	    /*@ non_null @*/ String resultVar,
	    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
	    throws NonExecutableQuantifierException 
	{
		if(transExp instanceof TransExpression){
			String var = varGen.freshVar();
			((TransExpression) transExp).PUT_ARGUMENT(var);
			expression.accept(transExp);
			RacNode stmt = (RacNode)((TransExpression) transExp).GET_RESULT();
			
			// JML collection type?
			if (expression.getType().isAlwaysAssignableTo(JML_COLLECTION)) {
				String i = varGen.freshVar();
				
				return RacParser.parseStatement(
						"org.jmlspecs.models.JMLCollection " + var + " = null;\n" +
						"$0\n" + 
						"for (java.util.Iterator " + i + 
						" = " + var + ".iterator();\n" +
						"     " + i + ".hasNext(); ) {\n" +
						"  " + resultVar + ".add(" + i + ".next());\n" +
						"}",
						stmt);
				
			} else { // JAVA_COLLECTION
				return RacParser.parseStatement(
						"java.util.Collection " + var + " = null;\n" +
						"$0\n" + 
						resultVar + ".addAll(" + var + ");",
						stmt);
			}
		}
		
		// TODO: FRioux - Handle TransExpression2
		else if(transExp instanceof TransExpression2){
			
			String var = varGen.freshVar();
			
			expression.accept(transExp);
			String stmt = ((TransExpression2) transExp).GET_RESULT();
			
			RacNode result = null;
			
			// JML collection type?
			if (expression.getType().isAlwaysAssignableTo(JML_COLLECTION)) {
				String i = varGen.freshVar();
				
				result = RacParser.parseStatement(
						"org.jmlspecs.models.JMLCollection " + var + " = " + stmt + ";\n" +
						"for (java.util.Iterator " + i + 
						" = " + var + ".iterator();\n" +
						"     " + i + ".hasNext(); ) {\n" +
						"  " + resultVar + ".add(" + i + ".next());\n" +
						"}");
				
			} else { // JAVA_COLLECTION
				result = RacParser.parseStatement(
						"java.util.Collection " + var + " = " + stmt + ";\n" +
						resultVar + ".addAll(" + var + ");");
			}
			
			//(FRioux) Can there be quantified statement to process as in Translator.transExpression() ???
    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
	    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
	    	}
    		
    		return result;

		}
		
		// should never happen
		return null;
		
	}
	
	public String translateAsString(
		    /*@ non_null @*/ VarGenerator varGen,
		    /*@ non_null @*/ String resultVar,
		    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
		    throws NonExecutableQuantifierException 
		{
			
			// TODO: FRioux - Handle TransExpression2
				
				String var = varGen.freshVar();
				
				expression.accept(transExp);
				String stmt = ((TransExpression2) transExp).GET_RESULT();
				
				String result = null;
				
				// JML collection type?
				if (expression.getType().isAlwaysAssignableTo(JML_COLLECTION)) {
					String i = varGen.freshVar();
					
					result = 
							"       org.jmlspecs.models.JMLCollection " + var + " = " + stmt + ";\n" +
							"       for (java.util.Iterator " + i + 
							" = " + var + ".iterator();\n" +
							"     " + i + ".hasNext(); ) {\n" +
							"  " + resultVar + ".add(" + i + ".next());\n" +
							"}";
					
				} else { // JAVA_COLLECTION
					result =
							"       java.util.Collection " + var + " = " + stmt + ";\n" +
							"       "+resultVar + ".addAll(" + var + ");\n";
				}
				
				//(FRioux) Can there be quantified statement to process as in Translator.transExpression() ???
//	    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
//	    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
//		    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
//		    	}
	    		
	    		return result;
			
		}

	/** JML expression for the qset. I.e., the prefix of a method
         * call expression. */
	private /*@ non_null @*/ JExpression expression;
    }

    /**
     * An abstract qset class consisting of two other qset objects, e.g.,
     * union or intersection qsets.
     */
    private static abstract class Composite extends QSet {
	/** 
	 * Constructs a new <code>Composite</code> object.
	 *
	 * @param left the left operand of the composite.
	 * @param right the right operand of the composite.
	 */
	protected Composite(QSet left, QSet right) {
	    this.left = left;
	    this.right = right;
	}

	/** left operand of the composite (union and intersection) */
	protected QSet left;

	/** right operand of the composite (union and intersection) */
	protected QSet right;
    }

    /**
     * A concrete qset class representating a union of two qsets.
     */
    private static class Union extends Composite {
	/** 
	 * Constructs a new <code>Union</code> object.
	 *
	 * @param left the left operand of the union.
	 * @param right the right operand of the union.
	 */
	private Union(QSet left, QSet right) {
	    super(left, right);
	}

	/** 
	 * Return Java source code that computes the qset represented by this
	 * object.
	 *
	 * @param varGen the variable generator to be used in the translation
	 *               for generating unique local variables.
	 * @param resultVar the variable name to refer to the qset object
	 *                  in the translated code.
	 * @param transExp the translator to use for translating JML 
	 *                 expressions.
	 */
	public RacNode translate(
	    /*@ non_null @*/ VarGenerator varGen,
	    /*@ non_null @*/ String resultVar,
	    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
	    throws NonExecutableQuantifierException 
	{
	    RacNode lstmt = left.translate(varGen, resultVar, transExp);
	    String var = varGen.freshVar();
	    RacNode rstmt = right.translate(varGen, var, transExp);
	    return RacParser.parseStatement(
	      "$0\n" +
	      "java.util.Collection " + var + " = new java.util.HashSet();\n" +
	      "$1\n" +
	      resultVar + ".addAll(" + var + ");",
	      lstmt, rstmt);
	}
	
	public String translateAsString(
		    /*@ non_null @*/ VarGenerator varGen,
		    /*@ non_null @*/ String resultVar,
		    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
		    throws NonExecutableQuantifierException 
		{
		    String lstmt = left.translateAsString(varGen, resultVar, transExp);
		    String var = varGen.freshVar();
		    String rstmt = right.translateAsString(varGen, var, transExp);
		    return 
		      lstmt +
		      "       java.util.Collection " + var + " = new java.util.HashSet();\n" +
		      rstmt + "       " + resultVar + ".addAll(" + var + ");\n";
		}
    }

    /**
     * A concrete qset class representating a qset that is an intersection of
     * two qsets.
     */
    private static class Intersection extends Composite {

	/** 
	 * Constructs a new <code>Intersection</code> object.
	 *
	 * @param left the left operand of the intersection.
	 * @param right the right operand of the intersection.
	 */
	private Intersection(QSet left, QSet right) {
	    super(left, right);
	}

	/** 
	 * Return Java source code that computes the qset represented by this
	 * object.
	 *
	 * @param varGen the variable generator to be used in the translation
	 *               for generating unique local variables.
	 * @param resultVar the variable name to refer to the qset object
	 *                  in the translated code.
	 * @param transExp the translator to use for translating JML 
	 *                 expressions.
	 */
	public RacNode translate(
	    /*@ non_null @*/ VarGenerator varGen,
	    /*@ non_null @*/ String resultVar,
	    /*@ non_null @*/ AbstractExpressionTranslator transExp) 
	    throws NonExecutableQuantifierException 
	{
	    RacNode lstmt = left.translate(varGen, resultVar, transExp);
	    String var = varGen.freshVar();
	    RacNode rstmt = right.translate(varGen, var, transExp);
	    return RacParser.parseStatement(
	      "$0\n" +
	      "java.util.Collection " + var + " = new java.util.HashSet();\n" +
	      "$1\n" +
	      resultVar + ".retainAll(" + var + ");",
	      lstmt, rstmt);
	}

	@Override
	public String translateAsString(VarGenerator varGen, String resultVar,
			AbstractExpressionTranslator transExp)
			throws NonExecutableQuantifierException {
		String lstmt = left.translateAsString(varGen, resultVar, transExp);
	    String var = varGen.freshVar();
	    String rstmt = right.translateAsString(varGen, var, transExp);
	    return 
	       lstmt +
	      "       java.util.Collection " + var + " = new java.util.HashSet();\n" +
	      rstmt + "       " + resultVar + ".retainAll(" + var + ");\n";
	}
    }

    
    /** Initializes collection types such as
     * <code>java.lang.Collection</code> and
     * <code>JMLCollection</code> recognized in translating quantified
     * expressions.
     */
    private static void initCollectionTypes() {
        if (JAVA_COLLECTION != null) {
            return;
        }            

        // find java.lang.Collection and JMLCollection
        try {
            JAVA_COLLECTION = 
                CTopLevel.getTypeRep("java/util/Collection",true);
            JML_COLLECTION =
                CTopLevel.getTypeRep("org/jmlspecs/models/JMLCollection",true);

        }
        catch (CompilationAbortedError e) {
            System.err.println("jmlc: can't load a required type " +
                               "Collection or JMLCollection!");
            System.exit(1);
        } 
        catch (CompilationAbortedException e) {
            System.err.println("jmlc: can't load a required type " +
                               "Collection or JMLCollection!");
            System.exit(1);
        }
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** Java collection type recognized in translating quantified
     * expressions.
     */
    private static CClassType JAVA_COLLECTION = null;

    /** JML model collection type recognized in translating quantified
     * expressions.
     */
    private static CClassType JML_COLLECTION = null;
}
