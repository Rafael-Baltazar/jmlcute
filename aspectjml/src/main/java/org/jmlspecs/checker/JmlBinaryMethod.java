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
 * $Id: JmlBinaryMethod.java,v 1.3 2003/11/01 00:39:36 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JLocalVariable;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a method read from a *.class file.  It is
 * primarily just a data structure, apart from methods for generating
 * the qualified name and for determining whether the member is
 * accessible from some class.
 */
public class JmlBinaryMethod extends JmlBinaryMember 
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class export from file. */
    public JmlBinaryMethod( TokenReference where, JmlSourceMethod member ) {
	super( where, member );
	CSpecializedType[] parmTypes = member.parameters();
	formals = new JFormalParameter[parmTypes.length];
	for (int i=0; i<parmTypes.length; i++) {
	    formals[i] = new JFormalParameter( where, 
					       JLocalVariable.DES_PARAMETER, 
					       parmTypes[i],
					       "",
					       false );
	}
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CMethod getMethod()
    {
	return (CMethod) member;
    }

    /**
     * @return	the name representation of this member.
     */
    public String stringRepresentation() {
	JmlSourceMethod self = (JmlSourceMethod) member;
	String thisStringRep = self.toString();
	int pos = thisStringRep.indexOf(".<init>");
	if (pos != -1) {
	    // 7 for length of ".<init>"
	    thisStringRep = thisStringRep.substring(0,pos)
		+ thisStringRep.substring(pos+7);
	}
	return thisStringRep;
    }

    // ----------------------------------------------------------------------
    // Interface methods for JMethodDeclarationType
    // ----------------------------------------------------------------------

    public /*@ pure @*/ JFormalParameter[] parameters() {
	return formals;
    }

    /** Returns the return type of this method declaration. If this
     * method declaration is a constructor, the returned object is the
     * object denoting the void type.
     */
    public /*@ pure @*/ CType returnType() {
	return getMethod().returnType();
    }

    /*
    public CClassType[] getExceptions() {
	return getMethod().exceptions();
    }
     */

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

    protected JFormalParameter[] formals;
}
