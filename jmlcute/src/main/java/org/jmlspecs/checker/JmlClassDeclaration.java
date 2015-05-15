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
 * $Id: JmlClassDeclaration.java,v 1.23 2006/12/13 21:09:05 wdietl Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JClassBlock;
import org.multijava.mjc.JClassDeclarationType;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This type represents a java class declaration in the syntax tree.
 */
public class JmlClassDeclaration extends JmlTypeDeclaration 
    implements JClassDeclarationType
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new JML class declaration; clients should use
     * factory method <Code>makeInstance</code> instead.  Because this
     * class and the super class both hold aliases to the same delegee
     * (to avoid casts during delegation), this constructor is
     * private.  */
    protected JmlClassDeclaration( TokenReference where,
				 boolean isWeakSubtype,
				 boolean[] interfaceWeaklyFlags,
				 JmlInvariant[] invariants,
				 JmlConstraint[] constraints,
				 JmlRepresentsDecl[] representsDecls,
				 JmlAxiom[] axioms,
				 JmlVarAssertion[] varAssertions,
				 JClassDeclarationWrapper delegee ) {
	super( where, interfaceWeaklyFlags, invariants, constraints, 
	       representsDecls, axioms, varAssertions, delegee );
	this.delegee = delegee;	// local reference avoids casts
	this.isWeakSubtype = isWeakSubtype;
    }

    /**
     * Constructs a class declaration in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	modifiers	the list of modifiers of this class
     * @param	ident		the short name of this class
     * @param	superType	the name of this class's superclass
     * @param	interfaces	the names of this types's interfaces
     * @param	methods	        a list of JMethodDeclarationTypes giving the
     *				methods of this type
     * @param	inners	        a list of JTypeDeclarations giving the
     *				inner classes (and interfaces) of this type
     * @param	fieldsAndInits	the fields and initializers of this type, 
     *				passed together because the order matters 
     *				for class and object initialization, members 
     *				of the array should be instances of 
     *				<code>JFieldDeclarationType</code> or 
     *				<code>JClassBlock</code>
     * @param	javadoc	        javadoc comments including whether this 
     *				type declaration is deprecated
     * @param	comment         regular java comments
     * @see JMethodDeclarationType
     * @see JFieldDeclarationType
     * @see JClassBlock
     */
    public static JmlClassDeclaration 
	makeInstance( TokenReference where,
		      long modifiers,
		      String ident,
              CTypeVariable[] typevariables,
		      //String superName, 
		      CClassType superType,
		      boolean isWeakSubtype,
		      CClassType[] interfaces, 
		      boolean[] interfaceWeaklyFlags,
		      ArrayList methods,
		      ArrayList inners,
		      JPhylum[] fieldsAndInits,
		      JmlInvariant[] invariants,
		      JmlConstraint[] constraints,
		      JmlRepresentsDecl[] representsDecls,
		      JmlAxiom[] axioms,
		      JmlVarAssertion[] varAssertions,
		      JavadocComment javadoc,
		      JavaStyleComment[] comment,
		      boolean isRefinedType)
    {
	JClassDeclarationWrapper delegee = 
	    new JClassDeclarationWrapper(where, modifiers, ident, typevariables, superType, 
		interfaces, methods, inners, fieldsAndInits, javadoc, comment,
	        isRefinedType);
	JmlClassDeclaration result = 
	    new JmlClassDeclaration(where, isWeakSubtype, interfaceWeaklyFlags,
	       invariants, constraints, representsDecls, axioms,
	       varAssertions, delegee );
	return result;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Returns true if this is a class declaration. */
    public /*@ pure @*/ boolean isClass() {
        return true;
    }

    public/*@ pure @*/  boolean isWeakSubtype() {
	return isWeakSubtype;
    }

    /** Is this class declaration runtime assertion checkable? This
     * method is used by jmlc. */
    public boolean isRacable() {
        return isRacable;
    }

    /** Indicates that this class declaration is runtime assertion
     * checkable. This method is used by jmlc. */
    public void setRacable() {
        isRacable = true;
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Sets the super class
     */
    public void setSuperClass(CClassType superType)
    {
	delegee.setSuperClass( superType );
    }

    /**
     * Sets the super class
     */
    public void setInterfaces(CClassType[] interfaces)
    {
	delegee.setInterfaces( interfaces );
    }

    /**
     * Creates a class context for this class declaration.
     * @param	parent		the parent context or null
     * @return	returns a CClassContextType that represents this context
     */
    public CClassContextType createContext(CContextType parent) {
	return delegee.createContext( parent);
    }

    public String superName()
    {
	return delegee.superName();
    }

    public boolean hasConstructor() {
	return delegee.hasConstructor();
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlClassDeclaration( this );
	else
	    super.accept( p );
    }

     /**
     * Computes the values of specializer expressions used to dispatch on
     * compile-time constants.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if the check fails */
    public void resolveSpecializers(CContextType context)
	throws PositionedError {
	delegee.resolveSpecializers( context );
    }

    //---------------------------------------------------------------------
    // PRIVATE DATA
    //---------------------------------------------------------------------

    protected JClassDeclarationWrapper delegee;

    private boolean isWeakSubtype;

    /** Is this class declaration runtime assertion checkable? This
     * flag is used by the jmlc. */
    private boolean isRacable = false; 
}
