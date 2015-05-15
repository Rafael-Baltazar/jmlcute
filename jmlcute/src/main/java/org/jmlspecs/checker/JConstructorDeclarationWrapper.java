/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
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
 * $Id: JConstructorDeclarationWrapper.java,v 1.8 2006/12/13 21:09:05 wdietl Exp $
 */


package org.jmlspecs.checker;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CMember;
import org.multijava.mjc.CSourceMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JConstructorBlock;
import org.multijava.mjc.JConstructorDeclaration;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.MemberAccess;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * A class representing a constructor declaration in the syntax tree. 
 * This class provides JML-specific handling of constructor declarations
 * by overriding several inherited methods. 
 * For example, the <code>checkInterface</code> method
 * now creates and returns an object of {@link JmlSourceMethod} instead of
 * {@link CSourceMethod}, that can handle JML-specific behaviors 
 * (e.g., spec_public-ness).
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.8 $
 */

public class JConstructorDeclarationWrapper extends JConstructorDeclaration
    implements Constants
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree
     * This method is directly called by the parser
     * @param	where		the line of this node in the source code
     * @param	modifiers	list of modifiers
     * @param	ident		the name of this method
     * @param	parameters	the parameters of this method
     * @param	exceptions	the exceptions throw by this method
     * @param	body		the body of this method, or null if abstract
     * @param	javadoc		is this constructor deprecated
     * @param	comments	regular Java comments 
     */
    public JConstructorDeclarationWrapper( TokenReference where,
                                           long modifiers, 
                                           String ident,
                                           JFormalParameter[] parameters,
                                           CClassType[] exceptions,
                                           JConstructorBlock body,
                                           JavadocComment javadoc,
                                           JavaStyleComment[] comments ) {
	super(where, modifiers, ident, parameters, exceptions, body, 
              javadoc, comments );
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /*
     * Checks the basic interfaces to make sure things generally look OK. 
     * This pass gathers information about the type signatures of everything 
     * (imported class files, classes being compiled, methods, fields, etc...)
     * needed for the later passes.  This information is stored 
     * in a context hierarchy that is bound to the AST.
     *
     * @param context the context in which this field appears
     * @return the signature of this field
     * @exception PositionedError an error with reference to the source file
     */
    public CMember checkInterface(CContextType context) 
	throws PositionedError 
    {
	return super.checkInterface(context);
    }

    /**
     * Generates the signature object for this method declaration. 
     * This method overrides the inherited method to generate JML-specific
     * signature object, i.e., an instance of {@link JmlSourceMethod}.
     */
    protected CSourceMethod makeMethodSignature( CContextType context,
						 MemberAccess access, 
						 String ident, 
					    CSpecializedType[] parameterTypes ) 
    {
	return ( new JmlSourceMethod( access, ident, returnType(),
				      parameterTypes, getExceptions(), 
				      CTypeVariable.EMPTY,
                                      isDeprecated(), body(), context, this ));
    }

    protected MemberAccess makeMemberAccess( CContextType context,
					     CClass owner )
    {
	return( new JmlMemberAccess( owner, 
				     context.findNearestHost(), 
				     modifiers() ));
    }
}
