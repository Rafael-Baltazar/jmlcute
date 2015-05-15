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
 * $Id: JmlMemberDeclaration.java,v 1.21 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CField;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.JMemberDeclaration;
import org.multijava.mjc.JMemberDeclarationType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This type represents a java declaration in the syntax tree.
 */
public abstract class JmlMemberDeclaration extends JmlNode
    implements JMemberDeclarationType
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlMemberDeclaration( /*@ non_null */ TokenReference where, 
				 /*@nullable@*/ JMemberDeclaration delegee ) {
	super( where );
	this.delegee = delegee;
    }
    

    // ----------------------------------------------------------------------
    // ACCESSORS (INTERFACE)
    // ----------------------------------------------------------------------

    /**
     * Returns true if this member is deprecated
     */
    public /*@ pure @*/ boolean isDeprecated()
    {
	return delegee.isDeprecated();
    }

    /**
     * @return	the field signature
     */
    public /*@ pure non_null @*/ CField getField()
    {
	return delegee.getField();
    }

    /**
     * @return	the method signature
     */
    public /*@ pure non_null@*/ CMethod getMethod()
    {
	return delegee.getMethod();
    }

    /**
     * @return	the type signature
     */
    public /*@ pure non_null @*/ CClass getCClass()
    {
	return delegee.getCClass();
    }

    /**
     * Generate the code in pure java form
     * It is useful to debug and tune compilation process
     * @param	p		the printwriter into the code is generated
     */
    public void genComments(/*@non_null@*/ MjcVisitor p)
    {
	delegee.genComments( p );
    }

    public /*@ pure @*/ /*@ nullable */ JavadocComment javadocComment()
    {
	return delegee.javadocComment();
    }

    // ----------------------------------------------------------------------
    // TYPE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Makes the general modifier consistency checks between refined 
     * declarations that are required of all refining members.
     * 
     */
    public void checkRefinedModifiers( /*@non_null@*/ CContextType context, 
				       /*@non_null@*/ JmlMemberDeclaration member ) 
	throws PositionedError 
    {
	if (member.isRefiningMember()) {
	    JmlMemberDeclaration refinedMember = member.getRefinedMember();
	    JmlMemberAccess memberAccess = member.jmlAccess();
	    String thisStringRep = member.stringRepresentation();
	    JmlMemberAccess refinedAccess = refinedMember.jmlAccess();
	    CClass refinedOwner = refinedAccess.owner();
	    java.io.File refinedFile = refinedOwner.sourceFile();
	    String refinedFileName = refinedFile.getName();

	    /*
	    System.out.println(thisStringRep+" static:"+access.isStatic()
			       +" model:"+access.isModel()
			       +" public:"+access.isPublic()
			       +" protected:"+access.isProtected()
			       +" private:"+access.isPrivate());
	     */

	    Object msgArgs[] = new Object[4];

	    // check to make sure the access modifiers match
	    msgArgs[1] = thisStringRep;
	    msgArgs[3] = refinedFileName;

	    // memberAccess.isStatic() <==> refinedMember.isStatic()
	    if ( memberAccess.isStatic() ) {
		msgArgs[0] = "Static";
		msgArgs[2] = "non-static";
		check( context,
		       refinedAccess.isStatic(),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-static";
		msgArgs[2] = "static";
		check( context,
		       !refinedAccess.isStatic(),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // memberAccess.isModel() <==> refinedAccess.isModel()
	    if ( memberAccess.isModel() ) {
		msgArgs[0] = "Model";
		msgArgs[2] = "non-model";
		check( context,
		       refinedAccess.isModel(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-model";
		msgArgs[2] = "model";
		check( context,
		       !refinedAccess.isModel(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // memberAccess.isFinal() <==> refinedAccess.isFinal()
	    if ( memberAccess.isFinal() ) {
		msgArgs[0] = "Final";
		msgArgs[2] = "non-final";
		check( context,
		       refinedAccess.isFinal(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-final";
		msgArgs[2] = "final";
		check( context,
		       !refinedAccess.isFinal(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }

	    // check to make sure the access levels match
	    msgArgs[1] = thisStringRep;
	    msgArgs[2] = refinedFileName;

	    if ( refinedAccess.isSpecPublic() ) {
		// refinedAccess.isSpecPublic() => memberAccess.isSpecPublic()
		msgArgs[0] = "Non-spec-public";
		msgArgs[3] = "spec-public";
		check( context,
		       memberAccess.isSpecPublic(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    }
	    if ( refinedAccess.isSpecProtected() ) {
		// refinedAccess.isSpecProtected() 
		//                   => memberAccess.isSpecProtected()
		msgArgs[0] = "Non-spec-protected";
		msgArgs[3] = "spec-protected";
		check( context,
		       memberAccess.isSpecProtected(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    }

	    if ( refinedAccess.isExplicitlyPublic() ) {
		// refinedAccess.isExplicitlyPublic() 
		//                   => memberAccess.isExplicitlyPublic()
		msgArgs[0] = "Non-public";
		msgArgs[3] = "public";
		check( context,
		       memberAccess.isExplicitlyPublic(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    } else if ( refinedAccess.isExplicitlyProtected() ) {
		// refinedAccess.isExplicitlyProtected() 
		//                    => memberAccess.isExplicitlyProtected())
		msgArgs[0] = "Non-protected";
		msgArgs[3] = "protected";
		check( context,
		       memberAccess.isExplicitlyProtected(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    } else if ( refinedAccess.isExplicitlyPrivate() ) {
		// refinedAccess.isExplicitlyPrivate() 
		//                    => memberAccess.isExplicitlyPrivate()
		msgArgs[0] = "Non-private";
		msgArgs[3] = "private";
		check( context,
		       memberAccess.isExplicitlyPrivate(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    } else if ( refinedAccess.hasDefaultAccess() ) {
		// refinedAccess.hasDefaultAccess() => memberAccess.isPrivate()
		msgArgs[0] = "Non-default visible";
		msgArgs[3] = "default";
		check( context,
		       memberAccess.hasDefaultAccess(),
		       JmlMessages.DIFFERENT_REFINING_ACCESS, 
		       msgArgs );
	    }
	}
    }

    /**
     * @return	the name representation of this member.
     */
    public /*@non_null@*/ String stringRepresentation() {
	return delegee.ident();
    }

    /**
     * @return	true iff this member refined by another member. 
     */
    public /*@ pure @*/ boolean isRefined() {
	return (refiningDecl != null);
    }

    /**
     * @return	true iff this member refines another member. 
     */
    public /*@ pure @*/ boolean isRefiningMember() {
	return (refinedDecl != null);
    }

    /**
     * Sets the field referencing the declaration refined by this declaration.
     */
    public void setRefinedMember(/*@ nullable */ JmlMemberDeclaration refinedDecl) {
	this.refinedDecl = refinedDecl;
    }

    /**
     * Sets the field referencing the declaration that refines this 
     * declaration.
     */
    public void setRefiningMember(/*@ nullable */ JmlMemberDeclaration refiningDecl) {
	this.refiningDecl = refiningDecl;
    }

    /**
     * @return	the member refined by this, or null if it does not refine 
     *          another member.
     */
    public /*@ pure @*/ /*@ nullable */ JmlMemberDeclaration getRefinedMember() {
	return refinedDecl;
    }

    /**
     * @return	the member that refines this, or null if it is not refined 
     *          by another member.
     */
    public /*@ pure @*/ /*@ nullable */ JmlMemberDeclaration getRefiningMember() {
	return refiningDecl;
    }

    public /*@ pure non_null@*/ JmlMemberDeclaration getMostRefined() {
	if (refiningDecl == null) {
	    return this;
	} else {
	    return refiningDecl.getMostRefined();
	}
    }

    public /*@ nullable */ String findJavaFileInRefinement() {
	if (this.inBinaryClassFile()) {
	    // The refined member is from a .class file so there is 
	    // a .java file and this file defines the interface for 
	    // the type (which can be used when checking the interface)
	    return this.getCClass().sourceFile().getName();
	} else if (this.inJavaFile()) {
	    return this.getTokenReference().file().getName();
	} else if (this.isRefiningMember()) {
	    return this.getRefinedMember().findJavaFileInRefinement();
	} else {
	    return null;
	}
    }

    /**
     * @return	the member access information object for this member.
     */
    public abstract /*@non_null@*/ JmlMemberAccess jmlAccess();

    /**
     *  Combine the specifications of this declaration with 
     *  the specifications of the declarations it refines.
     */
    public abstract void combineSpecifications();

    /**
     * Returns true if this member is declared in a '.java' file.
     */
    public boolean inJavaFile() {
	return jmlAccess().inJavaFile();
    }

    /**
     * Returns true if this member comes from a '.class' file.
     */
    public boolean inBinaryClassFile() {
	return false;
    }

    /**
     *  Returns null unless overridden by a subclass.
     *  Returns null if it does not have any combined method specifications.
     */
    public /*@ nullable */ JmlMethodSpecification getCombinedSpecification() {
	return null;
    }

    /**
     *  Returns null unless overridden by a subclass.
     *  Returns null if it does not have any combined variable assertions.
     */
    public /*@ pure @*/ /*@ nullable */ JmlVarAssertion[] getCombinedVarAssertions() {
	return null;
    }

    /**
     *  Returns null unless overridden by a subclass.
     *  Returns null if it does not have any inner type declarations.
     */
    public /*@ pure @*/ /*@ nullable */ ArrayList inners()
    {
	return null;
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Accepts the specified visitor
     * @param p	the visitor
     */
    public void accept(/*@non_null@*/ MjcVisitor p) {
	delegee.accept(p);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@nullable@*/ JMemberDeclaration delegee; // TODO: JmlBinaryMember calls the constructor with delegee == null. Is that intended?

    /**
     *  The declaration that is refined by this declaration.
     */
    protected /*@ nullable */ JmlMemberDeclaration refinedDecl = null;

    /**
     *  The declaration that refines this declaration.
     */
    protected /*@ nullable */ JmlMemberDeclaration refiningDecl = null;

}
