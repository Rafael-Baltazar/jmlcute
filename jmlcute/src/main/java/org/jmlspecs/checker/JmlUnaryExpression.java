/*
 * Copyright (C) 2003 Iowa State University.
 *
 * This file is part of jml, the Java Modeling Language Checker.
 *
 * based in part on work:
 *
 * Copyright (C) 2000-2001 Iowa State University
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id: JmlUnaryExpression.java,v 1.17 2004/07/10 03:36:02 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JNumberLiteral;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents unary expressions (unary plus, unary minus,
 * bitwise complement, and logical not).  */
public class JmlUnaryExpression extends JUnaryExpression implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	oper		the operator
     * @param	expr		the operand
     */
    public JmlUnaryExpression( TokenReference where, 
			     int oper, JExpression expr ) {
	super( where, oper, expr );
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    public CType getApparentType() {
	CType result = getType();
	if( result == JmlStdType.Bigint ) {
	    result = JmlStdType.Bigint; 
	} else if ( result == JmlStdType.Real ) {
	    result = CStdType.Double; // !FIXME! temp fix.
	} 
	return result;
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return  a desugared Java expression (see <code>JExpression.typecheck()</code>)
     * @exception PositionedError if the check fails
     */
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError 
    {

	// @see JUnaryExpression.typecheck()
	if( (expr instanceof JOrdinalLiteral) && oper == OPE_MINUS &&
	    ((JOrdinalLiteral)expr).isImageOnly() ) 
	{
	    ((JOrdinalLiteral) expr).negate();
	    oper = OPE_PLUS;
	}
    
	// At most unary minus is subject to implicit promotion.
	if(oper == OPE_MINUS && context.arithmeticMode().equals(AMID_BIGINT_MATH))
	{
	    // Call to typecheck to ensure getType() != null.
	    expr = expr.typecheck( context ); 
	    CType exprTp = expr.getType();

	    if(exprTp.isNumeric() && 
	       !exprTp.isFloatingPoint() && // TEMP: disable promotion to \real for now.
	       // If operand is constant, then attempt constant folding (and
	       // hence to not promote).
	       !expr.isConstant() &&
	       // No need to promote if operand is of type \bigint or \real.
		exprTp != JmlStdType.Bigint && exprTp != JmlStdType.Real)
	    {
		CType t = exprTp.isFloatingPoint()
		    ? JmlStdType.Real : JmlStdType.Bigint;

		expr = new JCastExpression(getTokenReference(), expr, t);
	    }
	    // Fall into another call to super.typecheck since we might
	    // have changed expr by adding a cast.
	}
	return super.typecheck( context );
    }
    
    /**
     * Override of super class method to issue warning if needed
     */
    protected JExpression noFolding( JExpression expr, CExpressionContextType context ) throws PositionedError{
    	
        // (unsafe) unary minus in a specification in java math mode
        if(Main.hasUnsafeOpWarningOption() && oper == OPE_MINUS && context.arithmeticMode().equals(AMID_JAVA_MATH)  && !((JMLMathMode)context.arithmeticMode()).isExplicitlySet() && context instanceof JmlContext && ((JmlContext) context).inSpecScope())
    	{
    		
    		// could merge the condition with the check...
    		try{
    			check(context,
    				expr.isConstant(),
    				JmlMessages.UNSAFE_ARITHMETIC_OPERATION, "-" 
    				);
    		} catch (PositionedError e){
    			context.reportTrouble(e);
    		}
    			
    	}	

    	return expr;
    }
    
    /**
     * Override of super class method to prevent constant folding 
     * @return	this
     */
    protected JExpression plusMinusConstantFolding(CExpressionContextType context)
    	throws PositionedError 
    {	
    
    if(Main.hasUnsafeOpWarningOption() &&  oper == OPE_MINUS && context.arithmeticMode().equals(AMID_JAVA_MATH) && !((JMLMathMode)context.arithmeticMode()).isExplicitlySet() && context instanceof JmlContext && ((JmlContext) context).inSpecScope()) {

        // Must create a new J*Literal as expr may be the value of a final
        // field which we do not want to alter (via negate()).
        JNumberLiteral lit = expr.getNumberLiteral();
        if( type.isOrdinal() ) {
            
            long v = lit.numberValue().longValue();
            try{
            	check( context, 
               		( type == CStdType.Integer
                 	? v != Integer.MIN_VALUE
                 	: v != Long.MIN_VALUE ),
               	JmlMessages.UNSAFE_ARITHMETIC_OPERATION, "-" );
            } catch (PositionedError e){
				context.reportTrouble(e);
			}
        }
    }	
    	
	JExpression result = this;

	if(type != JmlStdType.Bigint && type != JmlStdType.Real) {
	    try {
		result = super.plusMinusConstantFolding( context );
	    } catch( PositionedError e ) {
		// Folding overflowed.
		if( context.arithmeticMode().equals(AMID_JAVA_MATH) ) {
		    fail(); // i.e. this should never occur.
		}
		if( context.arithmeticMode().equals(AMID_SAFE_MATH) ) {
		    // don't promote
		    throw e;
		}	
		result = this;
		type = expr.getType().isFloatingPoint()
		    ? JmlStdType.Real : JmlStdType.Bigint;
	    }
	}
	// else do nothing as we do not fold over \bigint or \real.

	return result;
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    protected boolean do_const_folding = true;

}

