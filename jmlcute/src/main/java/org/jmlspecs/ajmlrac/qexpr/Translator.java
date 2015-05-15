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
 * $Id: Translator.java,v 1.5 2005/12/09 19:46:03 f_rioux Exp $
 */

package org.jmlspecs.ajmlrac.qexpr;

import org.jmlspecs.ajmlrac.*;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.multijava.mjc.JExpression;
import org.multijava.util.compiler.TokenReference;

/**
 * An abstract class for translating JML quantified expressions
 * into Java source code.
 */
abstract class Translator implements RacConstants {

    /**
     * Construct a <code>TransQuantifiedExpression</code> object.
     *
     * @param varGen variable generator to be used in translation for
     *               generating unique local variables.
     * @param expr quantified expression to be translated.
     * @param resultVar variable name to have the value of quantified
     *                  expression in the translated code.
     * @param transExp translator to use for translating subexpressions of
     *                 the quantified expression.
     */
    protected Translator (/*@ non_null @*/ VarGenerator varGen,
                          /*@ non_null @*/ RacContext ctx,
			  /*@ non_null @*/ JmlSpecQuantifiedExpression expr,
			  /*@ non_null @*/ String resultVar,
			  /*@ non_null @*/ AbstractExpressionTranslator transExp) {
	this.varGen = varGen;
        this.context = ctx;
	this.quantiExp = expr;
	this.resultVar = resultVar;
	this.transExp = transExp;
    }

    /**
     * Translate a JML quantified expression into Java source code 
     * and return the result.
     *
     * @return translated Java source code.
     * @throws NonExecutableQuantifierException if not executable.
     */
    public abstract RacNode translate() 
        throws NonExecutableQuantifierException;

    public abstract String translateAsString() 
    throws NonExecutableQuantifierException;
    /**
     * Returns a loop code that evaluates the given body with the 
     * quantified variable bound to each possible value of the range.
     *
     * @param body code to be executed as the loop body
     * @exception NonExecutableQuantifierException if not executable.
     */
    public abstract RacNode generateLoop(RacNode body) 
        throws NonExecutableQuantifierException;

    /** Returns code for evaluating expression <code>expr</code> and
     * storing the result to the variable <code>var</code>.
     * As a special case, returns <code>var = true;</code> 
     * if <code>expr</code> is null.
     */
    protected RacNode transExpression(JExpression expr, String var) {
    	
    	if(transExp instanceof TransExpression){
	    	// special handling for evaluating null range (predicate)
	    	// of quantified expression.
	    	if (expr == null)
	    		return RacParser.parseStatement(var + " = true;");
	    	
	    	((TransExpression) transExp).PUT_ARGUMENT(var);
	    	expr.accept(transExp);
	    	return (RacNode)((TransExpression) transExp).GET_RESULT();
    	}
    	
    	// Handle TransExpression2 (FRioux)
    	else if(transExp instanceof TransExpression2){
    		
    		// special handling for evaluating null range (predicate)
	    	// of quantified expression.
	    	if (expr == null)
	    		return RacParser.parseStatement(var + " = true;");  		
    		
			expr.accept(transExp);
			String stmt = ((TransExpression2) transExp).GET_RESULT();
    		
    		RacNode result = RacParser.parseStatement(var + " = " + stmt + ";");
    		System.out.println("------------->"+var + " = " + stmt + ";");
    		
    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
	    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
	    	}
    		
    		return result;
    			
    	}
    	
    	// should never happen
    	return null;
    }
    
    /** Returns code for evaluating expression <code>expr</code> and
     * storing the result to the variable <code>var</code>.
     * As a special case, returns <code>var = true;</code> 
     * if <code>expr</code> is null.
     */
    protected String transExpressionAsString(JExpression expr, String var) {
    	
    	if(transExp instanceof TransExpression){
	    	// special handling for evaluating null range (predicate)
	    	// of quantified expression.
	    	if (expr == null)
	    		return var + " = true;";
	    	
//	    	((TransExpression) transExp).PUT_ARGUMENT(var);
//	    	expr.accept(transExp);
//	    	return (RacNode)((TransExpression) transExp).GET_RESULT();
    	}
    	
    	// Handle TransExpression2 (FRioux)
    	else if(transExp instanceof TransExpression2){
    		
    		// special handling for evaluating null range (predicate)
	    	// of quantified expression.
	    	if (expr == null)
	    		return var + " = true;";  		
    		
			expr.accept(transExp);
			String stmt = ((TransExpression2) transExp).GET_RESULT();
    		
    		String result = var + " = " + stmt + ";";
    		
//    		if(((TransExpression2) transExp).hasPrebuiltNodes()){
//    			result = ((TransExpression2) transExp).addPrebuiltNode(result);
//	    		//throw(new NotImplementedExpressionException(quantiExp.getTokenReference(), "Nested JmlSpecQuantifiedExpression"));
//	    	}
    		
    		return result;
    			
    	}
    	
    	// should never happen
    	return null;
    }

    protected static final TokenReference NO_REF = TokenReference.NO_REF;

    /** variable generator for generating unique local variables */
    protected /*@ non_null @*/ VarGenerator varGen;

    /** current translation context */
    protected /*@ non_null @*/ RacContext context;

    /** taget quantified expression to translate */
    protected /*@ non_null @*/ JmlSpecQuantifiedExpression quantiExp;

    /** variable name to have the value of quantified expression 
     * in the translated code */
    protected /*@ non_null @*/ String resultVar;

    /* translator to use for translating subexpressions of
     * the quantified expression */
    protected /*@ non_null @*/ AbstractExpressionTranslator transExp;
}
