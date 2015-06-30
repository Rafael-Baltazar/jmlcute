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
 * $Id: JmlMinusExpression.java,v 1.7 2004/06/23 19:43:05 f_rioux Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;

import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents the addition binary expression.
 */
public class JmlMinusExpression extends JMinusExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree.
     * This method is directly called by the parser.
     * @param	where		the line of this node in the source code
     * @param	left		the left operand
     * @param	right		the right operand
     */
    public JmlMinusExpression( TokenReference where,
			   JExpression left,
			   JExpression right ) {
	super( where, left, right );
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return  a desugared Java expression (see <code>JExpression.typecheck()</code>)
     * @exception PositionedError if the check fails */
    public JExpression typecheck( CExpressionContextType context )
	throws PositionedError
    {
	JExpression[] lr =
	    JmlBinaryArithmeticExpressionHelper.typecheck(left,
							  right,
							  getTokenReference(),
							  context);
	left = lr[0];
	right = lr[1];
	return super.typecheck( context );
    }
    
    /**
     * Verify the operation. Overridden in JML to issue warnings.
     */
    public JExpression verifyOperation(JExpression expr,  CExpressionContextType context ){
    
    	return JmlBinaryArithmeticExpressionHelper.verifyOperation(expr, context, OPE_MINUS);
    }

    /**
     * Override of super class method to prevent constant folding (since in
     * general we might not be able to represent as a literal the difference
     * of two <code>\bigint</code>'s or <code>\real</code>'s.
     * @return	this
     */
    public JExpression constantFolding( CExpressionContextType context )
	throws UnpositionedError
    {
	JExpression result = this;

	if(type != JmlStdType.Bigint && type != JmlStdType.Real) {
	    try {
		result = super.constantFolding( context );
	    } catch( UnpositionedError e ) {
		// Folding overflowed.
				
		if( context.arithmeticMode().equals(AMID_JAVA_MATH) ) {
		    fail(); // i.e. this should never occur.
		}
		if( context.arithmeticMode().equals(AMID_SAFE_MATH) ) {
		    // don't promote
		    throw e;
		}	
		result = this;
		type = (left.getType().isFloatingPoint()
			|| right.getType().isFloatingPoint())
		    ? JmlStdType.Real : JmlStdType.Bigint;
	    }
	}
	// else do nothing as we do not fold over \bigint or \real.

	return result;
    }
    
    /**
     * Override of super class method to send the warning if the unsafe operation
     * result in an overflow when folding constants
     */
	public int compute(int left, int right, CExpressionContextType context) {

		JmlBinaryArithmeticExpressionHelper.compute(this, left, right, context, OPE_MINUS);
		return super.compute(left, right, context);
	}
	
    /**
     * Override of super class method to send the warning if the unsafe operation
     * result in an overflow when folding constants
     */
	public long compute(long left, long right, CExpressionContextType context) {

		JmlBinaryArithmeticExpressionHelper.compute(this, left, right, context, OPE_MINUS);
		return super.compute(left, right, context);
	}

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // VARIABLES
    // ----------------------------------------------------------------------

}
