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
 * $Id: JmlInterfaceDeclaration.java,v 1.23 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JClassBlock;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JInterfaceDeclarationType;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a java interface in the syntax tree
 */
public class JmlInterfaceDeclaration extends JmlTypeDeclaration 
    implements JInterfaceDeclarationType  
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /**
     * Constructs a new JML interface declaration; clients should use
     * factory method <Code>makeInstance</code> instead.  Because this
     * class and the super class both hold aliases to the same delegee
     * (to avoid casts during delegation), this constructor is
     * private. */
    protected JmlInterfaceDeclaration( /*@ non_null @*/ TokenReference where,
                     /*@ non_null */ boolean[] interfaceWeaklyFlags,
	                 /*@ non_null */ JmlInvariant[] invariants,
	                 /*@ non_null */ JmlConstraint[] constraints,
	                 /*@ non_null */ JmlRepresentsDecl[] representsDecls,
 		             /*@ non_null */ JmlAxiom[] axioms,
		       		 /*@ non_null */ JmlVarAssertion[] varAssertions,
				     /*@ non_null @*/ JInterfaceDeclarationWrapper delegee ) 
    {
	super( where, interfaceWeaklyFlags, invariants, constraints, 
	       representsDecls, axioms, varAssertions, delegee );
	this.delegee = delegee; // local reference avoids casts
    }    

    /**
     * Constructs an interface declaration in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	modifiers	the list of modifiers of this class
     * @param	ident		the short name of this class
     * @param	interfaces	the names of this types's interfaces
     * @param	methods	        a list of JMethodDeclarationTypes giving the
     *				methods of this type
     * @param	inners	        a list of JTypeDeclarationTypes giving the
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
    public static /*@non_null*/ JmlInterfaceDeclaration 
	makeInstance( /*@non_null*/TokenReference where,
		      long modifiers,
		      /*@non_null*/ String ident,
		      /*@non_null*/ CTypeVariable[] typevariables,
		      /*@non_null*/ CClassType[] interfaces,
		      /*@non_null*/ boolean[] interfaceWeaklyFlags,
		      /*@non_null*/ ArrayList methods,
		      /*@non_null*/ ArrayList inners,
		      /*@non_null*/ JPhylum[] fieldsAndInits,
		      /*@non_null*/ JmlInvariant[] invariants,
		      /*@non_null*/ JmlConstraint[] constraints,
		      /*@non_null*/ JmlRepresentsDecl[] representsDecls,
		      /*@non_null*/ JmlAxiom[] axioms,
		      /*@non_null*/ JmlVarAssertion[] varAssertions,
		      /*@nullable*/ JavadocComment javadoc,
		      /*@nullable*/ JavaStyleComment[] comment,
		      boolean isRefinedType)
    {
	JInterfaceDeclarationWrapper delegee = 
	    new JInterfaceDeclarationWrapper(where, modifiers, ident, typevariables,
					     interfaces, 
                methods, inners, fieldsAndInits, javadoc, comment,
					     isRefinedType);


	JmlInterfaceDeclaration result =
	    new JmlInterfaceDeclaration(where, interfaceWeaklyFlags, 
	       invariants, constraints, representsDecls, 
	       axioms, varAssertions, delegee );
	return result;
    }    

    // ----------------------------------------------------------------------
    // QUICK ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Returns true if this is an interface declaration. */
    public /*@ pure @*/ boolean isClass() {
        return false;
    }

    /** 
     * Returns all model fields inherited through the interface hierarchy.
     * This method must be called after typechecking.
     */
    public /*@non_null*/ JFieldDeclarationType[] getAllInterfaceModelFields()
    {
	Set s = new HashSet(Arrays.asList(this.getModelFields()));
	s.addAll(Arrays.asList(super.getAllInterfaceModelFields()));
	return (JFieldDeclarationType[])
		s.toArray(new JFieldDeclarationType[s.size()]);
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Creates an interface context for this interface declaration.
     * @param	parent		the parent context or null
     * @return	returns a CClassContextType that represents this context
     */
    public /*@ non_null @*/ CClassContextType createContext(/*@ non_null @*/ CContextType parent ) {
	return delegee.createContext( parent );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@non_null*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlInterfaceDeclaration(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    /**
     * Computes the values of specializer expressions used to dispatch on
     * compile-time constants.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if the check fails */
    public void resolveSpecializers(/*@ non_null @*/ CContextType context)
	throws PositionedError {
	delegee.resolveSpecializers( context );
    }

    //---------------------------------------------------------------------
    // PRIVILEGED MEMBERS
    //---------------------------------------------------------------------

    protected /*@ non_null @*/ JInterfaceDeclarationWrapper delegee;

}
