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
 * $Id: JmlBinaryMember.java,v 1.4 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CField;
import org.multijava.mjc.CMember;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.MemberAccess;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;


/**
 * This type represents a java declaration in the syntax tree.
 */
abstract public class JmlBinaryMember extends JmlMemberDeclaration
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlBinaryMember( TokenReference where, CMember member ) {
	super( where, null );
	this.member = member;
    }
    

    // ----------------------------------------------------------------------
    // ACCESSORS (INTERFACE)
    // ----------------------------------------------------------------------

    /**
     * Returns true if this member is deprecated
     */
    public /*@ pure @*/ boolean isDeprecated()
    {
	return member.isDeprecated();
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CField getField()
    {
	return null;
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CMethod getMethod()
    {
	return null;
    }

    /**
     * @return	the interface
     */
    public /*@ pure @*/ CClass getCClass()
    {
	return null;
    }

    /**
     * Generate the code in pure java form
     * It is useful to debug and tune compilation process
     * @param	p		the printwriter into the code is generated
     */
    public void genComments(MjcVisitor p)
    {
    }

    public /*@ pure @*/ JavadocComment javadocComment()
    {
	return null;
    }

    public /*@ pure @*/ String ident() {
	return member.ident();
    }

    /**
     * Returns true if this member is declared in a '.java' file.
     * We assume this member was declared in a '.java' file somewhere 
     * even though this data structure is created from a '.class' file.
     */
    public boolean inJavaFile() {
	return true;
    }

    /**
     * Always returns true since this member is from a '.class' file.
     */
    public boolean inBinaryClassFile() {
	return true;
    }

    // ----------------------------------------------------------------------
    // TYPE CHECKING
    // ----------------------------------------------------------------------

    /**
     * @return	the name representation of this member.
     */
    public String stringRepresentation() {
	return member.ident();
    }

    /**
     * @return	true iff this member refined by another member. 
     */
    public boolean isRefined() {
	return (refiningDecl != null);
    }

    /**
     * @return	true iff this member refines another member. 
     */
    public boolean isRefiningMember() {
	return (refinedDecl != null);
    }

    /**
     * @return	the member refined by this, or null if it does not refine 
     *          another member.
     */
    public JmlMemberDeclaration getRefinedMember() {
	return refinedDecl;
    }

    /**
     * @return	the member access information object for this member.
     */
    public JmlMemberAccess jmlAccess() {
	if (jmlAccess == null) {
	    MemberAccess acc = member.access();
	    if (acc instanceof JmlMemberAccess) {
		jmlAccess = (JmlMemberAccess) acc; 
	    } else {
		jmlAccess = new JmlMemberAccess(acc.owner(), 
						acc.host(), 
						acc.modifiers());
	    }
	}
	return jmlAccess;
    }

    /**
     *  Combine the specifications of this declaration with 
     *  the specifications of the declarations it refines.
     */
    public void combineSpecifications() {
    }

    public /*@ pure @*/ long modifiers() {
	return member.modifiers();
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Accepts the specified visitor
     * @param p	the visitor
     */
    public void accept(MjcVisitor p) {
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    protected CMember member;

    private JmlMemberAccess jmlAccess = null;
}
