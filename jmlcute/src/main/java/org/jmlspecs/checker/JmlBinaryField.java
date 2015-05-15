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
 * $Id: JmlBinaryField.java,v 1.2 2003/05/14 18:07:28 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CField;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a class read from a *.class file.  It is
 * primarily just a data structure, apart from methods for generating
 * the qualified name and for determining whether the member is
 * accessible from some class.
 *
 * @see	org.multijava.mjc.CMember
 */
public class JmlBinaryField extends JmlBinaryMember {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class export from file. */
    public JmlBinaryField( TokenReference where, CField member ) {
	super( where, member );
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CField getField()
    {
	return (CField) member;
    }

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

}
