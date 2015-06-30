/*  TransQuantifiedExpression.java,v 1.4 2002/06/24 21:46:23 leavens Exp $
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

import org.jmlspecs.ajmlrac.*;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.multijava.mjc.JVariableDefinition;

/**
 * An abstract class for translating JML quantified expressions into
 * Java source code. The translation rules for the JML
 * universal/existential quantified expressions are defined as
 * follows.
 *
 * <pre>
 *   [[(\forall T x; P; Q), r]] =
 *     Collection c = null;
 *     [[S, c]]  // S is the qset of P ==> Q
 *     r = c != null;
 *     if (r) {
 *        Iterator iter = c.iterator();
 *        for (r && iter.hasNext()) {
 *            T x = iter.next();
 *            [[P ==> Q, r]]
 *        }
 *     }
 * </pre>
 *
 * <pre>
 *   [[(\exists T x; P; Q), r]] =
 *     Collection c = null;
 *     [[S, c]]  // S is the qset of P && Q
 *     r = c == null;
 *     if (!r) {
 *        Iterator iter = c.iterator();
 *        for (!r && iter.hasNext()) {
 *            T x = iter.next();
 *            [[P && Q, r]]
 *        }
 *     }
 * </pre>
 *
 * The translation rules for other quantifiers are defined in a
 * similar way.
 *
 * @see TransExpression#visitJmlSpecQuantifiedExpression( 
 *      JmlSpecQuantifiedExpression)
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.16 $
 */

public class TransQuantifiedExpression {


    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new instance. 
     *
     * @param varGen variable generator to be used during translation to 
     *               generate unique local variables.
     * @param expr quantified expression to be translated.
     * @param resultVar variable name to have the value of quantified
     *                  expression in the translated code.
     * @param transExp translator to use for translating subexpressions of
     *                 the quantified expression.
     */
	public TransQuantifiedExpression(
			/*@ non_null @*/ VarGenerator varGen,
			/*@ non_null @*/ RacContext context,
			/*@ non_null @*/ JmlSpecQuantifiedExpression expr,
			/*@ non_null @*/ String resultVar,
			/*@ non_null @*/ AbstractExpressionTranslator transExp) {
		
		this.varGen = varGen;
		this.context = context;
		this.quantiExp = expr;
		this.resultVar = resultVar;
		this.transExp = transExp;
		
		
		if(transExp instanceof TransExpression2){
			JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
			String evaluatorPUse = "";
			String evaluatorPDef = "";
			for (int i = 0; i < varDefs.length ; i++) {
				if(i == 0){
					evaluatorPUse = varDefs[i].ident();
					evaluatorPDef = TransUtils.toString( varDefs[i].getType()) + " " + varDefs[i].ident();
				}
				else{
					evaluatorPUse = evaluatorPUse + ", " + varDefs[i].ident();
					evaluatorPDef = evaluatorPDef + ", " + TransUtils.toString( varDefs[i].getType()) + " " + varDefs[i].ident();
				}
			}
			
			((TransExpression2)transExp).setEvaluatorPUse(evaluatorPUse);
			((TransExpression2)transExp).setEvaluatorPDef(evaluatorPDef);
		}
		
	}


    // ----------------------------------------------------------------------
    // TRANSLATION
    // ----------------------------------------------------------------------

    /**
     * Translates a JML quantified expression into Java source code
     * and return the translated code. Refers to 
     * {@link TransQuantifiedExpression} for the format of the generated
     * code.
     *
     * @return translated Java source code.
     * @throws if the quantified expression is not executable.
     */
    public RacNode translate() {
    	  	
    	// a set of tranlators that can translate quantified expressions
    	// into Java source code.
    	Translator[] translators = {
    			StaticAnalysis.getInstance(varGen, context, quantiExp, resultVar, transExp)
    	};
    	
    	for (int i = 0; i < translators.length; i++) {
    		try {
    			//return translators[i].translate();
    			RacNode result = translators[i].translate();
    			
    	    	// Debugging info (FRioux)
    	    	// result = RacParser.parseStatement("// -------QUANTIFIER-------\n$0\n// -------QUANTIFIER (end)-------", result);
    			
    			return result;
    		}
    		catch (NonExecutableQuantifierException e) {
    			// try next translator
    		}
    	}
    	
    	if(transExp instanceof TransExpression){
    		TransExpression.warn(quantiExp.getTokenReference(), RacMessages.NOT_EXECUTABLE,	"This quantifier");
    	}
    	
    	if(transExp instanceof TransExpression2){
    		throw(new NonExecutableExpressionException(quantiExp.getTokenReference(), "this quantifier"));
    	}
    	
    	return nonExecutableQuantifiedExpression();
    }
    
    /**
     * Translates a JML quantified expression into Java source code
     * and return the translated code. Refers to 
     * {@link TransQuantifiedExpression} for the format of the generated
     * code.
     *
     * @return translated Java source code.
     * @throws if the quantified expression is not executable.
     */
    public String translateAsString() {
    	  	
    	// a set of tranlators that can translate quantified expressions
    	// into Java source code.
    	Translator[] translators = {
    			StaticAnalysis.getInstance(varGen, context, quantiExp, resultVar, transExp)
    	};
    	
    	for (int i = 0; i < translators.length; i++) {
    		try {
    			//return translators[i].translate();
    			String result = translators[i].translateAsString();
    			
    	    	// Debugging info (FRioux)
    	    	// result = RacParser.parseStatement("// -------QUANTIFIER-------\n$0\n// -------QUANTIFIER (end)-------", result);
    			
    			return result;
    		}
    		catch (NonExecutableQuantifierException e) {
    			// try next translator
    		}
    	}
    	
    	if(transExp instanceof TransExpression){
    		TransExpression.warn(quantiExp.getTokenReference(), RacMessages.NOT_EXECUTABLE,	"This quantifier");
    	}
    	
    	if(transExp instanceof TransExpression2){
    		throw(new NonExecutableExpressionException(quantiExp.getTokenReference(), "this quantifier"));
    	}
    	
//    	return nonExecutableQuantifiedExpression();
    	return "";
    }

    /**
     * Tanslates a JML quantified expression into Java source code
     * that, if executed, evaluates the given statement,
     * <code>node</code> for each combination of bound variables of
     * the quantified expression. For example, given a quantified expression
     *
     * <pre>
     * (\forall int i; 
     *   i >= 0 && i < this.v.length; 
     *     this.v[i] >= \old(this.v[i]))
     * </pre>
     *
     * this method generates the following code:
     * <pre>
     * int i = 0;
     * int l = this.v.length;
     * while (i < l) {
     *   [[code for argument node]]
     *   i = i + 1;
     * }
     * </pre>
     *
     * where <code>l</code> is a unique local variable generated by
     * the runtime assertion checker compiler.
     *
     * This method is used in translating old expressions contained in 
     * quantified expressions.
     *
     * @return translated Java source code.
     * @throws if the quantified expression is not executable.
     *
     * @see TransPostcondition#visitJmlOldExpression(JmlOldExpression)
     * @see TransPostcondition#oldExpressionInQuantifiers(JmlOldExpression)
     */
    public RacNode generateLoop(RacNode node) 
        throws NonExecutableQuantifierException {

	// a set of tranlators that can translate quantified expressions 
        // into Java source code.
	Translator[] translators = {
	    StaticAnalysis.getInstance(varGen, context, quantiExp, resultVar,
                                       transExp)
	};

	for (int i = 0; i < translators.length; i++) {
	    try {
		return translators[i].generateLoop(node);
	    }
	    catch (NonExecutableQuantifierException e) {
                // try next translator
	    }
	}
	
	if(transExp instanceof TransExpression2){
		throw(new NonExecutableExpressionException(quantiExp.getTokenReference(), "this quantifier"));
	}
	
	throw new NonExecutableQuantifierException();
    }

    // ----------------------------------------------------------------------
    // HELPER METHODS
    // ----------------------------------------------------------------------

    /** Translates a non-executable quantified expression. A
     * boolean-typed quantified expression is translated into
     * <code>resultVar = true/false;</code>, if the contextual
     * translation is enabled. Otherwise, it is translated into the
     * following code:
     *
     * <pre>
     *  if (true) {
     *    throw new JMLNonExecutableException();
     *  }
     * </pre>
     * 
     * A non-boolean typed quantified expression is also translated
     * into the above <code>if</code> statement.
     */
    private RacNode nonExecutableQuantifiedExpression() {
        String code = "// from non-executable quantified expression\n";
        if (context.enabled() && quantiExp.getType().isBoolean()) {
            code = context.angelicValue(resultVar) + ";";
        } else {
            code = "if (true) {\n" + // prevent reachability analysis errors
                   "  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
                   "}";
        }
        return RacParser.parseStatement(code);
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** variable generator for generating unique local variables. */
    private /*@ non_null @*/ VarGenerator varGen;

    /** Current translation context. */
    private RacContext context;

    /** quantified expression to be translated. */
    private /*@ non_null @*/ JmlSpecQuantifiedExpression quantiExp;

    /** variable name to store the value of quantified expression
     * in the translated code. */
    private /*@ non_null @*/ String resultVar;

    /** translator for translating subexpressions */
    private /*@ non_null @*/ AbstractExpressionTranslator transExp;
}
