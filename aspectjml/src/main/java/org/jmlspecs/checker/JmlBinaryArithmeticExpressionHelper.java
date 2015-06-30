/*
 * Copyright (C) 2003 Iowa State University
 *
 * This file is part of jml, the Java Modeling Language Checker.
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
 * $Id: JmlBinaryArithmeticExpressionHelper.java,v 1.10 2004/07/09 15:55:41 f_rioux Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JPhylum;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class is an abstract root class for binary expressions.
 */
public class JmlBinaryArithmeticExpressionHelper implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /* None. Only contains static methods for now. */

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
    public static JExpression[] typecheck( JExpression left,
					   JExpression right,
					   TokenReference where,
					   CExpressionContextType context )
	throws PositionedError
    {
    	
	if((context.arithmeticMode().equals(AMID_BIGINT_MATH))
	   // && !(left instanceof JCastExpression) && !(right instanceof JCastExpression)
	   ) {
	    // Call to compute types (as they might not be defined yet).
	    left = left.typecheck( context );
	    right = right.typecheck( context );

	    CType leftTp  = left.getType();
	    CType rightTp = right.getType();

	    if(leftTp.isNumeric() && rightTp.isNumeric() &&
	       !leftTp.isFloatingPoint() && // TEMP: disable promotion to \real for now.
	       !rightTp.isFloatingPoint() && // TEMP: disable promotion to \real for now.
	       // If both operands are constant, then let us assume that
	       // constant folding will occur (without implicit promotion).
	       !(left.isConstant() && right.isConstant())
	       &&
	       // Optimization: no need for implicit promotion if either
	       // operand is of type \bigint or \real.
	       leftTp  != JmlStdType.Bigint && leftTp  != JmlStdType.Real &&
	       rightTp != JmlStdType.Bigint && rightTp != JmlStdType.Real
	       ) {
		CType t = (leftTp.isFloatingPoint() || rightTp.isFloatingPoint()) 
		    ? JmlStdType.Real : JmlStdType.Bigint;

		left = new JCastExpression(where, left, t);
		right = new JCastExpression(where, right, t);
	    }
    	}
	JExpression[] lr = { left, right };
	return lr;
    }
    
    public static JExpression verifyOperation(JExpression expr,
			CExpressionContextType context, int oper) {

		String sign;
		if (oper == OPE_PLUS)
			sign = "+";
		else if (oper == OPE_MINUS)
			sign = "-";
		else if (oper == OPE_STAR)
			sign = "*";
		else if (oper == OPE_SLASH)
			sign = "/";
		else
			return expr; // this method should not have been called

		// (unsafe) binary operation in a specification in java math mode
		if (Main.hasUnsafeOpWarningOption()
				&& context.arithmeticMode() instanceof JMLMathMode
				&& context.arithmeticMode().equals(AMID_JAVA_MATH)
				&& !((JMLMathMode) context.arithmeticMode()).isExplicitlySet()
				&& context instanceof JmlContext
				&& ((JmlContext) context).inSpecScope()) {
			try {
				expr.check(context, false, JmlMessages.UNSAFE_ARITHMETIC_OPERATION,
						sign);
			} catch (PositionedError e) {
				context.reportTrouble(e);
			}
		}

		return expr;
	}
    
	public static void compute(JExpression expr, int left, int right,
			CExpressionContextType context, int oper) {

		String sign = "";

		if (Main.hasUnsafeOpWarningOption()
				&& context.arithmeticMode().equals(AMID_JAVA_MATH)
				&& !((JMLMathMode) context.arithmeticMode()).isExplicitlySet()
				&& context instanceof JmlContext
				&& ((JmlContext) context).inSpecScope()) {
			try {
				if (oper == OPE_PLUS) {
					sign = "+";
					((JmlAddExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_MINUS) {
					sign = "-";
					((JmlMinusExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_STAR) {
					sign = "*";
					((JmlMultExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_SLASH) {
					sign = "/";
					((JmlDivideExpression) expr).safe_compute(left, right);
				} else {
					return; // this method should not have been called
				}
			} catch (UnpositionedError err) {
				// in java mode, no error... but a warning
				try {
					((JPhylum)expr).check(context, false,
							JmlMessages.UNSAFE_ARITHMETIC_OPERATION, sign);
				} catch (PositionedError e) {
					context.reportTrouble(e);
				}
			}
		}
		return;
	}
	
	public static void compute(JExpression expr, long left, long right,
			CExpressionContextType context, int oper) {

		String sign = "";

		if (Main.hasUnsafeOpWarningOption()
				&& context.arithmeticMode().equals(AMID_JAVA_MATH)
				&& !((JMLMathMode) context.arithmeticMode()).isExplicitlySet()
				&& context instanceof JmlContext
				&& ((JmlContext) context).inSpecScope()) {
			try {
				if (oper == OPE_PLUS) {
					sign = "+";
					((JmlAddExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_MINUS) {
					sign = "-";
					((JmlMinusExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_STAR) {
					sign = "*";
					((JmlMultExpression) expr).safe_compute(left, right);
				} else if (oper == OPE_SLASH) {
					sign = "/";
					((JmlDivideExpression) expr).safe_compute(left, right);
				} else {
					return; // this method should not have been called
				}
			} catch (UnpositionedError err) {
				// in java mode, no error... but a warning
				try {
					((JPhylum)expr).check(context, false,
							JmlMessages.UNSAFE_ARITHMETIC_OPERATION, sign);
				} catch (PositionedError e) {
					context.reportTrouble(e);
				}
			}
		}
		return;
	}
    
}
