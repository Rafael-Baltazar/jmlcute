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
 * $Id: JmlBitwiseExpression.java,v 1.1 2003/06/10 19:38:17 f_rioux Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.JBitwiseExpression;
import org.multijava.mjc.JExpression;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents the addition binary expression.
 */
public class JmlBitwiseExpression extends JBitwiseExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree
     * This method is directly called by the parser
     * @param	where		the line of this node in the source code
     * @param	oper		the operator
     * @param	left		the left operand
     * @param	right		the right operand
     */
    public JmlBitwiseExpression( TokenReference where,
    			   int oper,
			   JExpression left,
			   JExpression right ) {
	super( where, oper, left, right );
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

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // VARIABLES
    // ----------------------------------------------------------------------

}
