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
 * $Id: JmlOrdinalLiteral.java,v 1.3 2004/01/22 19:59:30 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CNumericType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents jml specific ordinal literals (bigint)
 */
public class JmlOrdinalLiteral extends JOrdinalLiteral {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree
     * @param where  the line of this node in the source code
     * @param image  the string representation of this literal
     */
    public JmlOrdinalLiteral(TokenReference where, String image) {
	super(where, image);
    }

    /**
     * Construct a node in the parsing tree
     * @param where  the line of this node in the source code
     * @param value  the value of this literal
     * @param type   the type of this literal
     */
    public JmlOrdinalLiteral(TokenReference where, Number value, CNumericType type) {
	super(where, value, type);
    }

    /**
     * Construct a node in the parsing tree
     * @param where  the line of this node in the source code
     * @param value  the value of this literal
     * @param type   the type of this literal
     */
    public JmlOrdinalLiteral(TokenReference where, long value, CNumericType type) {
	super(where, value, type);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Returns a Number that represents the value of this literal.
     */
    public Number numberValue() {
	if (getType() == JmlStdType.Bigint) {
	    return value;
	} else {
	    return super.numberValue();
	}
    }


    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * convertType
     * changes the type of this expression to another
     * @param	dest	the destination type
     * @param	context	the context in which this expression appears
     */
    public JExpression convertType( CType dest, CExpressionContextType context) 
	throws PositionedError 
    {
	if( type == null ) {
	    calculateType();
	}
	if( dest == JmlStdType.Bigint ) {
	    return new JOrdinalLiteral( getTokenReference(),
					new Long(value.longValue()),
					JmlStdType.Bigint);
	} else {
	    return super.convertType(dest, context);
	}
    }
}
