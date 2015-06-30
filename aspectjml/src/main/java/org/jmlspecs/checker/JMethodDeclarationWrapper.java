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
 * $Id: JMethodDeclarationWrapper.java,v 1.16 2007/04/24 06:40:26 smshaner Exp $
 */


package org.jmlspecs.checker;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSourceMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.MemberAccess;
import org.multijava.util.Utils;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * A class representing a method declaration in the syntax tree. 
 * This class provides JML-specific handling of method declarations
 * by overriding several inherited methods. 
 * For example, the <code>makeMethodSignature</code> method
 * now creates and returns an object of {@link JmlSourceMethod} instead of
 * {@link CSourceMethod}, that can handle JML-specific behaviors 
 * (e.g., spec_public-ness).
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.16 $
 */

public class JMethodDeclarationWrapper extends JMethodDeclaration
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
     * @param	returnType	the return type of this method
     * @param	ident		the name of this method
     * @param	parameters	the parameters of this method
     * @param	exceptions	the exceptions throw by this method
     * @param	body		the body of this method
     * @param	javadoc		javadoc comments, including whether this 
     *				method is deprecated
     * @param	comments	regular java style comments
     */
    public JMethodDeclarationWrapper(TokenReference where,
				     long modifiers,
                                     CTypeVariable[] typevariables,
				     CType returnType,
				     String ident,
				     JFormalParameter[] parameters,
				     CClassType[] exceptions,
				     JBlock body,
				     JavadocComment javadoc,
				     JavaStyleComment[] comments ) {
	super(where, modifiers, typevariables, returnType, ident, 
	      parameters, exceptions, body, javadoc, comments);
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
    public CMember checkInterface(CContextType context) 
	throws PositionedError 
    {
	return super.checkInterface(context);
    }
     */


    /**
     * Generates the signature object for this method declaration. 
     * This method overrides the inherited method to generate JML-specific
     * signature object, i.e., an instance of {@link JmlSourceMethod}.
     *
     */
    protected CSourceMethod makeMethodSignature( CContextType context,
						 MemberAccess access, 
						 String ident, 
					    CSpecializedType[] parameterTypes ) 
    {
	return new JmlSourceMethod( access, ident, returnType(),
				      parameterTypes, getExceptions(), 
				      typevariables(),
                                      isDeprecated(), body(), context, this );
    }

    protected MemberAccess makeMemberAccess( CContextType context,
					     CClass owner )
    {
	return( new JmlMemberAccess( owner, 
				     context.findNearestHost(), 
				     modifiers() ));
    }

    /**
     * Returns true iff this method is abstract or is a model method.
     */
    public boolean isModel() {
	long modifiers = modifiers();
	return Utils.hasFlag(modifiers, ACC_MODEL);
    }

    /**
     * Returns true iff this method should have its model program extracted per SLN 07.
     */
    public boolean shouldExtract() {
	long modifiers = modifiers();
	return Utils.hasFlag(modifiers, ACC_EXTRACT);
    }

    protected boolean noBodyOK(CContextType context, CMethod self) {
	return isModel() || super.noBodyOK(context,self); 
    }

    /**
     * Checks that this method appropriately overrides the given
     * superclass methods.  The checks are those given in JLS2,
     * section 8.4.6.3 and CLCM 00 4.1.3.1 (extended per Clifton's
     * thesis).
     *
     * <pre><jml>
     * also requires context != null && superMethods != null;
     * </jml></pre>
     *
     * @param	context		the context in which this appears
     * @param	superMethods	the super types methods that this
     *                          <em>may</em> override.
     * @exception PositionedError if a check fails */
    public void checkOverriding( CContextType context, CMethodSet superMethods )
	throws PositionedError 
    {
	super.checkOverriding( context, superMethods );

	// some JML checks of modifiers
	JmlSourceMethod self = (JmlSourceMethod) getMethod();
	JmlMemberAccess selfAccess = self.jmlAccess();

	// checks the superMethods as a whole without differentiating
	int size = superMethods.size();
	for( int i=0; i<size; i++ ) {

	    CMethod superMethod = superMethods.getMethod( i );
	    Object msgArgs[] = new Object[4];
	    if (superMethod instanceof JmlSourceMethod) {
		JmlMemberAccess superAccess 
		    = ((JmlSourceMethod)superMethod).jmlAccess();
		CClass superOwner = superAccess.owner();
		java.io.File superFile = superOwner.sourceFile();
		String superFileName = Utils.relativePathTo(superFile);

		msgArgs[1] = self.toString();
		msgArgs[3] = superFileName;

		// superAccess.isModel() <==> selfAccess.isModel()
		if ( superAccess.isModel() ) {
		    msgArgs[0] = "Non-model";
		    msgArgs[2] = "model";
		    check( context,
			   selfAccess.isModel(), 
			   JmlMessages.METHOD_MODIFIER_MISMATCH, 
			   msgArgs  );
		} else {
		    msgArgs[0] = "Model";
		    msgArgs[2] = "non-model";
		    check( context,
			   ! selfAccess.isModel(), 
			   JmlMessages.METHOD_MODIFIER_MISMATCH, 
			   msgArgs  );
		}
	    } else {
		// the superclass method is not a model method
		msgArgs[0] = "Model";
		msgArgs[2] = "non-model";
		check( context,
		       ! selfAccess.isModel(), 
		       JmlMessages.METHOD_MODIFIER_MISMATCH, 
		       msgArgs  );
	    }
	}
    }

    public void typecheck( CContextType context )
	throws PositionedError
    {
	super.typecheck(context);

	if (this.shouldExtract()) {
	    JmlSourceMethod self = (JmlSourceMethod) getMethod();
	    JmlMemberAccess selfAccess = self.jmlAccess();
	    
	    selfAccess.checkInterfaceMethodModifiers(context, this);
	    
	    check(context,
		  !selfAccess.isAbstract(),
		  JmlMessages.ILLEGAL_EXTRACT_MODIFIER);
	}
    }
}
