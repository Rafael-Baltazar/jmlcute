/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
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
 * $Id: CTypeType.java,v 1.8 2004/01/22 19:59:28 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClassFQNameType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CType;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents the JML \TYPE type.
 * It is derived from CClassType and has the specific value of 
 * java.lang.Class, with the exception that it prints out (via toString)
 * as "TYPE".  Thus it compares equal to (via equals()) to CStdType.Class.
 * @see	org.multijava.mjc.CType
 */
public class CTypeType extends CClassFQNameType implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructor
     */
    protected CTypeType() {
	super(org.multijava.mjc.Constants.JAV_CLASS);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Transforms this type to a string
     */
    public String toString() {
	return "\\TYPE";
    }

    
    /**
     * Returns the type identifier. The return value is TID_TYPE.
     */
    //@ pure
    public int getTypeID() {
        return TID_TYPE;
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Compute the value of a specializer expression used to dispatch on
     * a compile-time constant.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if the check fails */
    public void resolveValueType(CExpressionContextType context)
	throws PositionedError {}
    
    
    // ----------------------------------------------------------------------
    // BODY CHECKING
    // ----------------------------------------------------------------------

    /**
     * Is this type assignable to the given type by assignment type
     * conversion [JLS2 5.2].
     * @param	dest		the destination type
     * @return true iff assignment is valid */
    public boolean isAlwaysAssignableTo(CType dest) {
	return dest.equals(JmlStdType.TYPE);
    }

    /**
     * Can this type be converted to the specified type by casting
     * conversion (JLS 5.5) ?
     * @param	dest		the destination type
     * @return true iff the casting conversion is valid */
    public boolean isCastableTo(CType dest) {
	return dest.equals(JmlStdType.TYPE);
    }
}
