/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
 * *
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
 * $Id: JmlSourceMethod.java,v 1.34 2006/12/13 21:09:05 wdietl Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlMethodInfo;
import org.jmlspecs.util.classfile.JmlMethodable;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CSourceMethod;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.MemberAccess;
import org.multijava.util.classfile.CodeInfo;
import org.multijava.util.classfile.MethodInfo;
/**
 * A class for representing JML method declaration in the signature forest.
 * It includes the type signature of the method and operations for
 * checking the method's applicability and whether it is more specfic 
 * than a given method. 
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.34 $
 */
public class JmlSourceMethod extends CSourceMethod 
    implements JmlMethodable, Constants
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    public JmlSourceMethod( MemberAccess access, 
			    String ident, CType returnType,
			    CSpecializedType[] paramTypes, 
			    CClassType[] exceptions,
                            CTypeVariable[] typevariables, boolean deprecated, 
			    JBlock body, CContextType declarationContext, 
			    JMethodDeclaration declarationASTNode )
    {
	super( ((access instanceof JmlMemberAccess) ?
		access 
		: (new JmlMemberAccess(access.owner(), 
				       access.host(),
				       access.modifiers()))
		), 
	       ident, returnType, paramTypes, exceptions, typevariables, 
	       deprecated, body, declarationContext, declarationASTNode );
    }
    public JmlSourceMethod(CSourceMethod method) {
	super(method.access(), 
	      method.ident(), method.returnType(), method.parameters(),
	      method.throwables(), method.getTypeVariable(),
	      method.deprecated(), method.body(),
	      method.declarationContext(),
	      (JMethodDeclaration) method.declarationASTNode());
    }

    // ----------------------------------------------------------------------
    // CHECK MATCHING
    // ----------------------------------------------------------------------

    /**
     * Returns true iff this method should be treated as a model method;
     * the method itself is model or it is declared inside a model class
     * or interface.
     */
    public /*@ pure @*/ boolean isEffectivelyModel() {
	if (!(owner() instanceof JmlSourceClass)) {
	    throw new IllegalStateException("JML implementation error");
	}

	return isModel() ||
	   (owner() != null && ((JmlSourceClass)owner()).isEffectivelyModel());
    }

    /**
     * Returns true iff this field is explicitly declared as model.
     */
    public /*@ pure @*/ boolean isModel() {
	return jmlAccess().isModel();
    }

    /** Returns true if this method is a model method and can be
     * executed by simply commenting out annotation markers. This
     * method must be called after typechecking. */
    public /*@ pure @*/ boolean isExecutableModel() {
        if (!isModel() || 
            ((JmlSourceClass) owner()).isEffectivelyModel()) {
            return false;
        }

        return isConstructor() ? body().body() != null :
            body() != null;
    }

    /**
     * Returns true if this method is applicable to a method call with
     * the given identifier and actual (static) argument types. This method
     * refines the inherited method to make model methods applicable only 
     * in specfication contexts (i.e., in spec scope).
     *
     * @param	ident		the identifier to match
     * @param	recvType	receiver type	
     * @param	actuals		the method call static argument types
     * @return true if this method is applicable 
     * @see CMethod#isApplicable(String, CType, CType[])
     */
    public boolean isApplicable(String ident, CType recvType,
                                CType[] actuals,CClassType[] args) {
	boolean result = super.isApplicable(ident, recvType, 
					    actuals,args);

	// model methods are visible only in spec scope
	if (result && isEffectivelyModel()) {
	    result = JmlContext.inSpecScope();
	}
	return result;
    }

    /**
     * Returns true if the file in which this member is declared is 
     * a '.java' file.
     */
    public /*@ pure @*/ boolean inJavaFile() {
	return jmlAccess().inJavaFile();
    }

    /**
     * Returns true if this member is public, including spec_public
     * in a JML specification scope.
     * @see #isProtected()
     * @see #isPrivate()
     */
    public /*@ pure @*/ boolean isPublic() {
	if (JmlContext.inSpecScope()) {
	    if (isSpecPublic()) {
		return true;
	    }
	    if (isSpecProtected()) {
		return false;
	    }
	}
	long mod = modifiers();
	return hasFlag(mod, ACC_PUBLIC);
    }

    /**
     * Returns true if this member is protected, including spec_protected
     * in a JML specification scope.
     * @see #isPublic()
     * @see #isPrivate()
     */
    public /*@ pure @*/ boolean isProtected() {
	if (JmlContext.inSpecScope()) {
	    if (isSpecProtected()) {
		return true;
	    }
	    if (isSpecPublic()) {
		return false;
	    }
	}
	long mod = modifiers();
	return hasFlag(mod, ACC_PROTECTED);
    }

    /**
     * Returns true if this member is private. In a JML specification
     * scope, it also means not being spec_public nor spec_protected.
     * @see #isProtected()
     * @see #isPublic()
     */
    public /*@ pure @*/ boolean isPrivate() {
	if (JmlContext.inSpecScope() &&
	    (isSpecPublic() || isSpecProtected())) {
	    return false;
	}
	long mod = modifiers();
	return hasFlag(mod, ACC_PRIVATE);
    }

    /** Returns true if this method is spec_public. */
    public /*@ pure @*/ boolean isSpecPublic() {
        return hasFlag(modifiers(), ACC_SPEC_PUBLIC);
    }

    /** Returns true if this method is spec_protected. */
    public /*@ pure @*/ boolean isSpecProtected() {
        return hasFlag(modifiers(), ACC_SPEC_PROTECTED);
    }

    /** Returns always false. This is a dumb method to implement the
     * interface JmlMethodable.
     */
    public boolean isGhost() {
        return false;
    }

    public String getGenericSignature() {
	return getSignature();
    }

    /**
     * Returns the parameters (AST's) for this method.
     */
    public /*@ pure @*/ JFormalParameter[] getASTparameters() {
	if (methodAST instanceof JmlMethodDeclaration) {
	    return ((JmlMethodDeclaration)methodAST).parameters();
	} else {
	    return ((JmlBinaryMethod)methodAST).parameters();
	}
    }

    /**
     * Sets the AST for this method.
     */
    public void setAST(JmlMemberDeclaration methAST) 
    {
	this.methodAST = methAST;
    }

    /**
     * Returns the AST for this method.
     */
    public /*@ pure @*/ JmlMemberDeclaration getAST() {
	return methodAST;
    }

    /**
     * Returns the most refined declaration AST for this method.
     */
    public /*@ pure @*/ JmlSourceMethod getMostRefined() {
	CMethod mostRefinedDecl = methodAST.getMostRefined().getMethod();
	return (JmlSourceMethod) mostRefinedDecl;
    }

    /**
     * Returns the specification AST for this method.
     */
    public /*@ pure @*/ JmlMethodSpecification getSpecification() {
	if (methodAST instanceof JmlMethodDeclaration) {
	    return ((JmlMethodDeclaration)methodAST).methodSpecification();
	} else {
	    return null;
	}
    }

    public /*@ pure @*/ boolean isRefined() {
	return methodAST.isRefined();
    }


    // ----------------------------------------------------------------------
    // JmlRefinableSourceType INTERFACE methods
    // ----------------------------------------------------------------------

    /**
     * @return	the member access information object for this member.
     */
    public /*@ pure @*/ JmlMemberAccess jmlAccess() {
        return (JmlMemberAccess) access();
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Creates a method info object. This is a factory method that may
     * be overridden by the subclass.
     */
    protected MethodInfo createCMethodInfo(int modifiers,
                                           String name,
                                           String type,
                                           String[] exceptions, 
                                           CSourceMethod method,
                                           boolean deprecated,
                                           boolean synthetic) {
        return new JmlMethodInfo(modifiers, name, type, exceptions,
                                 method, deprecated, synthetic);
    }
    
    /**
     * Creates a method info object. This is a factory method that may
     * be overridden by the subclass.
     */
    protected MethodInfo createMethodInfo(int modifiers,
                                          String name,
                                          String type,
                                          String[] exceptions, 
                                          CodeInfo code,
                                          boolean deprecated,
                                          boolean synthetic) {
        return new JmlMethodInfo(modifiers, name, type, exceptions,
                                 code, deprecated, synthetic);
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
    
    private JmlMemberDeclaration methodAST = null;
}
