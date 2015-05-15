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
 * $Id: JmlBinaryType.java,v 1.6 2003/10/12 05:24:48 cruby Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.mjc.CAbstractMethodSet;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CMethodSet;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a class read from a *.class file.  It is
 * primarily just a data structure that contains information for 
 * checking the signatures in a refinement sequence.  
 *
 * @see	org.multijava.mjc.CMember
 */
public class JmlBinaryType extends JmlBinaryMember {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class export from file. */
    public JmlBinaryType( TokenReference where, 
			  JmlBinarySourceClass member, 
			  String prefix )
	throws PositionedError 
    {
	super( where, member );

	member.setAST(this);
	CClassType[] innerTypes = member.getInnerClasses();
	inners = new ArrayList(innerTypes.length);
	for (int i=0; i<innerTypes.length; i++) {
	    String innerIdent = innerTypes[i].ident();
	    JmlBinaryType innerType 
		= JmlRefinePrefix.buildBinaryType( where, 
						   prefix + "$" + innerIdent );
	    inners.add(innerType);
	}
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CClass getCClass()
    {
	return (CClass) member;
    }

    /** This method collects the AST's for the binary methods 
     *  declared in the original source file; they are 
     *  used to make sure there are no "extra" non-model methods 
     *  declared in the specification files.  Non-model methods must be 
     *  declared in the API for this type.
     */
    public void combineSpecifications() {
	CClass clazz = (JmlBinarySourceClass) member;
	CMethodSet methodSet = clazz.methods();
	ArrayList tempList = new ArrayList(methodSet.size());
	CAbstractMethodSet.Iterator iter = methodSet.iterator();
	while (iter.hasNext()) {
	    JmlSourceMethod meth = (JmlSourceMethod) iter.next();
	    tempList.add(meth.getAST());
	}
	methods = new JmlMemberDeclaration[tempList.size()];
	tempList.toArray(methods);
    }

    public JmlMemberDeclaration[] getCombinedMethods()
    {
	if (methods == null) {
	    combineSpecifications();
	}
	return methods;
    }

    public /*@ pure @*/ ArrayList inners()
    {
	return inners;
    }

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

    protected JmlMemberDeclaration[] methods = null;

    protected ArrayList inners = null;
}
