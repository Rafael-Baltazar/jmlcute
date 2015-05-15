/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
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
 * $Id: JmlConstructorDeclaration.java,v 1.10 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.javadoc.JavadocComment;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlConstructorDeclaration.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.10 $
 */

public class JmlConstructorDeclaration extends JmlMethodDeclaration 
    implements JConstructorDeclarationType
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    private JmlConstructorDeclaration( TokenReference where,
				       JmlMethodSpecification methodSpecification,
				       JConstructorDeclaration delegee) {
	super( where, methodSpecification, delegee );
	this.delegee = delegee;
    }
    
    public static JmlConstructorDeclaration
	makeInstance( TokenReference where, long modifiers, String ident, 
		      JFormalParameter[] params, CClassType[] exceptions,
		      JConstructorBlock body, JavadocComment javadoc,
		      JavaStyleComment[] comments, 
		      JmlMethodSpecification methodSpecification ) {
	JConstructorDeclaration delegee =
	    new JConstructorDeclarationWrapper( where, modifiers, ident, 
                params, exceptions, body, javadoc, comments );
	return new JmlConstructorDeclaration( where, methodSpecification,
					      delegee );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public boolean hasBody() { 
	return delegee.hasBody();
    }

    /** Returns true if this declaration is for a constructor. */
    public /*@ pure @*/ boolean isConstructor() {
        return true;
    }

    /** Returns true if this constructor is a model constructor and
     * can be executed by simply commenting out annotation
     * markers. This method must be called after typechecking. */
    public /*@ pure @*/ boolean isExecutableModel() {
        return isModel() && hasBody() &&
            !((JmlSourceClass) getMethod().owner()).isEffectivelyModel();
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlConstructorDeclaration( this );
	else
	    super.accept( p );
    }

    public void acceptDelegee( MjcVisitor p ) {
	p.visitConstructorDeclaration(delegee);
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this method declaration.  Mutates the context to
     * record the information gathered during the checks.
     *
     * @param cContext the context in which this method appears
     * @param instanceInfo the definite-assignment state of the surrounding
     *                     class after instance initializers but before any
     *                     constructors
     * @exception PositionedError if the checks fail and the failure
     * cannot be recovered from */
    public void typecheck( CClassContextType cContext, 
			   CVariableInfoTable instanceInfo) 
	throws PositionedError
    {
	this.instanceInfo = instanceInfo;
	cContext.setFieldInfoTable(instanceInfo);
	typecheck(cContext);
	this.instanceInfo = null;
    }

    /**
     * Resets the final field definite assignment info if this is a
     * constructor.
     */
    protected void resetFinalFieldStatusIfConstructor(CClassContextType context){
	context.setFieldInfoTable(instanceInfo);
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JConstructorDeclaration delegee;

    /**
     * Temporarily stores the final field definite assignment
     * information while typechecking the constructor.
     */
    private CVariableInfoTable instanceInfo;
   
}// JmlConstructorDeclaration
