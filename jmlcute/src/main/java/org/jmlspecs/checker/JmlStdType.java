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
 * $Id: JmlStdType.java,v 1.11 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;

/**
 * This class is a singleton that provides variables for the various
 * built-in and java.lang types.  
 */
public class JmlStdType extends CStdType implements Constants {

    // ----------------------------------------------------------------------
    // PRIMITIVE TYPES
    // ----------------------------------------------------------------------

    public static /*@non_null@*/ JmlNumericType	Bigint;
    public static /*@non_null@*/ JmlNumericType	Real;

    //---------------------------------------------------------------------
    // REFERENCE TYPES
    //---------------------------------------------------------------------

    public static /*@non_null@*/ CTypeType TYPE;
    public static /*@non_null@*/ CClassType JMLObjectSet;

    // ----------------------------------------------------------------------
    // INITIALIZERS
    // ----------------------------------------------------------------------

    static {
	// PC TBC - !FIXME! Might have to extend PRIMITIVE_TYPES[] ...
	Bigint = new JmlNumericType(TID_BIGINT);
	Real = new JmlNumericType(TID_REAL);
	initHelper();
    }

    private static void initHelper() {
	TYPE =  new CTypeType();
	JMLObjectSet = CTopLevel.getTypeRep(Constants.JML_JMLObjectSet,true);
    }
    
    /**
     * Re-initializes static fields for the next compilation session.
     */
    static public void initSession() {
	initHelper();
    }
}
