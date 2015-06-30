/*
 * Copyright (C) 2000-2005 Iowa State University
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
 * $Id: JmlMemberAccess.java,v 1.20 2007/04/24 05:11:47 smshaner Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CMember;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.JFieldDeclaration;
import org.multijava.mjc.JMemberDeclaration;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JTypeDeclaration;
import org.multijava.mjc.MemberAccess;
import org.multijava.mjc.MjcMessages;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents and contains the information needed to determine 
 * whether a member of a class or compilation unit can be accessed 
 * from some other member.  
 * It has the interface checking code for ensuring that modifiers 
 * are valid for the member containing it, 
 * e.g., class, field, and method signature classes.
 * The modifier checking code was factored out of 
 * <code>JmlTypeDeclaration</code>, <code>JmlFieldDeclaration</code>, and   
 * <code>JmlMethodDeclaration</code> rather than using callbacks so 
 * the modifier checking could all be done in one class.  
 *
 * @see	CMember
 */

public class JmlMemberAccess extends MemberAccess implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a member export
     * @param	owner		the owner of this field
     * @param	modifiers	the modifiers on this field
     */
    public JmlMemberAccess(CClass owner, long modifiers) {
	super(owner, modifiers);
    }

    /**
     * Constructs a top-level member export
     * @param	owner		the owner of this member
     * @param	host		the host of this member's declaration
     * @param	modifiers	the modifiers on this member
     */
    public JmlMemberAccess(CClass owner, CMemberHost host, long modifiers )
    {
	super(owner, host, modifiers);
    }

    /**
     * Indicates whether this is accessible from the given host.
     *
     * @param	member	the member that needs to be accessed
     * @param	from	the host that wants to access member
     * @return	true iff the given host is allowed access to this member
     */
    public /*@ pure @*/ boolean isMemberVisibleInX( CMember member, 
						   CMemberHost from ) 
    {
        // !FIXME! disabled as it gives lots of test failures
        if (!JmlContext.inSpecScope() && (isModel() || isGhost())) {
            return false;
        }
        return super.isMemberVisibleIn(member, from);
    }

    /**
     * Returns true if this member is declared in a '.java' file.
     */
    public /*@ pure @*/ boolean inJavaFile() {
	CMemberHost host = host();
	if (host instanceof JmlSourceClass) {
	    return ((JmlSourceClass)host).inJavaFile();
	}
	return false;
    }

    /**
     * Returns true if this member is public, including spec_public
     * in a JML specification scope.
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
	return hasFlag(modifiers, ACC_PUBLIC);
    }

    /**
     * Returns true if this member is protected, including spec_portected
     * in a JML specification scope.
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
	return hasFlag(modifiers, ACC_PROTECTED);
    }

    /**
     * Returns true if this member is private. In a JML specification
     * scope, it also means not being spec_public nor spec_protected.
     */
    public /*@ pure @*/ boolean isPrivate() {
	if ( JmlContext.inSpecScope() 
	     && (isSpecPublic() || isSpecProtected()) ) {
	    return false;
	}
	return hasFlag(modifiers, ACC_PRIVATE);
    }

    /**
     * Returns true iff this member has a public modifier. 
     */
    public boolean isExplicitlyPublic() {
	return hasFlag(modifiers, ACC_PUBLIC);
    }

    /**
     * Returns true iff this member has a protected modifier. 
     */
    public boolean isExplicitlyProtected() {
	return hasFlag(modifiers, ACC_PROTECTED);
    }

    /**
     * Returns true if this member has a private modifier. 
     */
    public boolean isExplicitlyPrivate() {
	return hasFlag(modifiers, ACC_PRIVATE);
    }

    // ----------------------------------------------------------------------
    // JML MODIFIERS
    // ----------------------------------------------------------------------

    /** Returns true if this member is spec_public. */
    public /*@ pure @*/ boolean isSpecPublic() {
        return hasFlag(modifiers, ACC_SPEC_PUBLIC);
    }

    /** Returns true if this member is spec_protected. */
    public /*@ pure @*/ boolean isSpecProtected() {
        return hasFlag(modifiers, ACC_SPEC_PROTECTED);
    }

    /**
     * Returns true if this member is pure. A member is pure if it is
     * annotated with the JML <code>pure</code> modifier.
     */
    public /*@ pure @*/ boolean isPure() {
        return hasFlag(modifiers, ACC_PURE);
    }

    /**
     * Returns true if this member is query. A member is query if it is
     * annotated with the JML <code>query</code> modifier.
     */
    public /*@ pure @*/ boolean isQuery() {
        return hasFlag(modifiers, ACC_QUERY);
    }

    /**
     * Returns true if this member is secret. A member is secret if it is
     * annotated with the JML <code>secret</code> modifier.
     */
    public /*@ pure @*/ boolean isSecret() {
        return hasFlag(modifiers, ACC_SECRET);
    }

    /**
     * Returns true if this member is a model. It is a model member 
     * if it is annotated with the JML <code>model</code> modifier.
     */
    public /*@ pure @*/ boolean isModel() {
        return hasFlag(modifiers, ACC_MODEL);
    }

    /**
     * Returns true if this member is a ghost variable. A member is a
     * ghost variable if it is annotated with the JML
     * <code>ghost</code> modifier.
     */
    public /*@ pure @*/ boolean isGhost() {
        return hasFlag(modifiers, ACC_GHOST);
    }

    /**
     * Returns true if this member is a instance variable. It is an 
     * instance variable if it is annotated with the JML 
     * <code>instance</code> modifier.
     */
    public /*@ pure @*/ boolean isInstance() {
        return hasFlag(modifiers, ACC_INSTANCE);
    }

    /**
     * Returns true if this member is a helper method. A member is a helper 
     * if it is annotated with the JML <code>helper</code> modifier.
     */
    public /*@ pure @*/ boolean isHelper() {
        return hasFlag(modifiers, ACC_HELPER);
    }

    /**
     * Returns true if this member is a monitored field. A member is 
     * monitored if it is annotated with the JML <code>monitored</code> 
     * modifier.
     */
    public boolean isMonitored() {
        return hasFlag(modifiers, ACC_MONITORED);
    }

    /**
     * Returns true if this member is an uninitialized field. A member is 
     * uninitialized if it is annotated with the JML <code>uninitialized</code> 
     * modifier.
     */
    public /*@ pure @*/ boolean isUninitialized() {
        return hasFlag(modifiers, ACC_UNINITIALIZED);
    }

    /** Returns the privacy of this declaration. If the modifiers has
     * either SPEC_PUBLIC or SPEC_PROTECTED, then that access modifier
     * takes a precedence over the JAVA access modifiers.
     */
    protected /*@ pure @*/ long privacy() {
        // can have multiple access modifiers, so explicitly
        // check from the most visible to the least visible ones.
        if (hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_PUBLIC))
            return ACC_PUBLIC;
        else if (hasFlag(modifiers, ACC_SPEC_PROTECTED | ACC_PROTECTED))
            return ACC_PROTECTED;
        else if (hasFlag(modifiers, ACC_PRIVATE))
            return ACC_PRIVATE;
        else
            return 0L; // package
    }
    
    /**
     * Returns the arithmetic mode of the code (or -1 if not specified)
     */
    public JMLMathMode codeArithmeticMode(){
        //to avoid too much function calls, here is a local copy of some of
        //the booleans used to perform checking
        boolean code_java_math = hasFlag(modifiers, ACC_CODE_JAVA_MATH);
        boolean code_safe_math = hasFlag(modifiers, ACC_CODE_SAFE_MATH);
        boolean code_bigint_math = hasFlag(modifiers, ACC_CODE_BIGINT_MATH);
        boolean code_default = !(code_java_math||code_safe_math||code_bigint_math);

        //Code Arithemetic Mode
        if(!code_default){
        	if(code_java_math) {return JMLMathMode.newJMLMathMode(AMID_JAVA_MATH);}
        	else if(code_safe_math) {return JMLMathMode.newJMLMathMode(AMID_SAFE_MATH);}
        	else if(code_bigint_math) {return JMLMathMode.newJMLMathMode(AMID_BIGINT_MATH);}
        	else {fail();}
        }
        
        //Default of a method is its class mode
        if(host!=null && host instanceof org.jmlspecs.checker.JmlSourceClass && code_default){
        	return ((JmlSourceClass)host).jmlAccess().codeArithmeticMode();
        }
        
        //Default of a class is java math mode
        //return new JMLMathMode(AMID_JAVA_MATH);
        return JMLMathMode.newJMLMathMode();
    }
    
    /**
     * Returns the arithmetic mode of the spec (or -1 if not specified)
     */
    public JMLMathMode specArithmeticMode(){
        //to avoid too much function calls, here is a local copy of some of
        //the booleans used to perform checking
        boolean spec_java_math = hasFlag(modifiers, ACC_SPEC_JAVA_MATH);
        boolean spec_safe_math = hasFlag(modifiers, ACC_SPEC_SAFE_MATH);
        boolean spec_bigint_math = hasFlag(modifiers, ACC_SPEC_BIGINT_MATH);
        boolean spec_default = !(spec_java_math||spec_safe_math||spec_bigint_math);     
          		
        //Spec Arithemetic Mode
        if(!spec_default){
        	if(spec_java_math) {return JMLMathMode.newJMLMathMode(AMID_JAVA_MATH);}
        	else if(spec_safe_math) {return JMLMathMode.newJMLMathMode(AMID_SAFE_MATH);}
        	else if(spec_bigint_math) {return JMLMathMode.newJMLMathMode(AMID_BIGINT_MATH);}
        	else {fail();}
        }
        
        //Default of a method is its class mode
        if(host!=null && host instanceof org.jmlspecs.checker.JmlSourceClass && spec_default){
        	return ((JmlSourceClass)host).jmlAccess().specArithmeticMode();
        }
        
        //Default of a class is java math mode
        //return new JMLMathMode(AMID_JAVA_MATH);
        return JMLMathMode.newJMLMathMode();
    }

    // ----------------------------------------------------------------------
    // MODIFIER CHECKS
    // ----------------------------------------------------------------------

    /**
     * Check illegal combinations of modifiers common to classes,
     * interfaces, fields, and methods.
     */
    public void checkAccessModifiers( CContextType context,
				      JMemberDeclaration member )
	throws PositionedError
    {
	// check the modifier combinations allowed in all Java/MJC declarations
        super.checkAccessModifiers( context, member );

        // SPEC_PUBLIC and SPEC_PROTECTED
        member.check(context, 
		     !( isSpecPublic() && isSpecProtected() ),
		     JmlMessages.FLAG_SPEC_PUBLIC_AND_PROTECTED);

        // MODEL and SPEC_PUBLIC/PROTECTED
        member.check(context, 
		     !( isModel() && (isSpecPublic() || isSpecProtected()) ),
		     JmlMessages.FLAG_MODEL_AND_SPEC_PUBLIC);

        // SPEC_PUBLIC/PROTECTED can't narrow Java's visibility.
        member.check(context, 
		     !( isSpecPublic() && super.isPublic() ),
		     JmlMessages.FLAG_SPEC_PUBLIC);
        member.check(context, 
		     !( isSpecProtected() 
			&& (super.isPublic() || super.isProtected()) ),
		     JmlMessages.FLAG_SPEC_PROTECTED);
    }

    /**
     * Check for illegal combinations of modifiers specific to classes 
     * and interfaces.
     */
    public void checkClassModifiers( CContextType context,
				     JTypeDeclaration member )
	throws PositionedError
    {
	// check the MJC/Java class modifiers
        super.checkClassModifiers( context, member );

        // Check allowed JML modifiers in class and interface declarations 
	member.check(context, 
		     !hasFlag(modifiers, invalidJmlClassModifiers),
		     JmlMessages.CLASS_FLAGS);

	member.check(context,
	      !(hasFlag(modifiers, Constants.ACC_NULLABLE_BY_DEFAULT) 
		&& hasFlag(modifiers, Constants.ACC_NON_NULL_BY_DEFAULT)),
	      JmlMessages.CLASS_LEVEL_NULLABLE_NON_NULL_TOGETHER
	      );
    }

    /**
     * Check for illegal combinations of modifiers specific to field 
     * declarations.
     */
    public void checkFieldModifiers( CContextType context,
				     JFieldDeclaration member )
	throws PositionedError
    {
	// check the MJC field modifiers
        super.checkFieldModifiers( context, member );


        // Check allowed JML modifiers in field declarations 
	member.check(context, 
		     !hasFlag(modifiers, invalidJmlFieldModifiers),
		     JmlMessages.FIELD_FLAGS);

        // Check illegal combinations of allowed modifiers
        
        // MODEL and FINAL
        member.check(context, 
		     !(isModel() && isFinal()),
		     JmlMessages.FLAG_MODEL_AND_FINAL);
        
        // MODEL and GHOST
        member.check(context, 
		     !(isModel() && isGhost()),
		     JmlMessages.FLAG_MODEL_AND_GHOST);

        // GHOST and SPEC_PUBLIC/PROTECTED
        member.check(context, 
		     !(isGhost() && (isSpecPublic() || isSpecProtected())),
		     JmlMessages.FLAG_GHOST_AND_SPEC_PUBLIC);

        // INSTANCE and STATIC
        member.check(context, 
		     !(isInstance() && isStatic()),
		     JmlMessages.FLAG_INSTANCE_AND_STATIC);

        // INSTANCE without MODEL or GHOST
        member.check(context, 
		     !(isInstance() && !(isModel() || isGhost())),
		     JmlMessages.FLAG_INSTANCE_WITHOUT_MODEL);

	member.check(context, 
		     !(hasFlag(modifiers, ACC_NON_NULL) && hasFlag(modifiers, ACC_NULLABLE)),
		     JmlMessages.NULLABLE_NON_NULL_TOGETHER);
    }

    /**
     * Check for illegal combinations of modifiers disallowed in 
     * interface field declarations.
     *
     * Adds the default public, static, and final modifiers (not done 
     * for model/ghost fields);
     * these default modifiers are the only ones allowed for fields 
     * declared in interfaces. 
     *
     * @return	the new set of modifiers 
     */
    public long checkInterfaceFieldModifiers( CContextType context,
					     JFieldDeclaration member )
	throws PositionedError
    {
	if (owner().isInterface()) {
	    long modsBefore = modifiers;
	    // check the MJC interface field modifiers
	    super.checkInterfaceFieldModifiers( context, member );

	    // MJC field modifier checking adds public, final, and static 
	    // modifiers to interface fields. The added final has to be 
	    // removed from "model/ghost" fields and the static modifier 
	    // has to be removed from instance "model/ghost" fields. 

	    if (isModel() || isGhost()) {
		if (!hasFlag(modsBefore, ACC_FINAL)) {
		    removeFinalModifier();
		}
                if (isInstance()) {
                    if (!hasFlag(modsBefore, ACC_STATIC)) {
			removeStaticModifier();
                    }
                }
	    }
	    member.check(context, 
			 !(hasFlag(modifiers, ACC_NON_NULL) && hasFlag(modifiers, ACC_NULLABLE)),
			 JmlMessages.NULLABLE_NON_NULL_TOGETHER);
	}
	return modifiers;
    }

    /**
     * Check for illegal combinations of modifiers specific to method 
     * declarations.
     */
    public void checkMethodModifiers( CContextType context,
				      JMethodDeclaration member )
	throws PositionedError
    {
	// check the MJC/Java method modifiers
	super.checkMethodModifiers( context, member );

        // Check allowed JML modifiers in method declarations 
        member.check(context, 
		     !hasFlag(modifiers, invalidJmlMethodModifiers),
		     JmlMessages.METHOD_FLAGS);
        
	// helper modifier only for private methods --- this rule has changed in OpenJML. --- [[[hemr]]]
    // a pure non-constructor method can be helper even if it has no private visibility --- [[[hemr]]]
        if (isHelper()) {
            if(isPure()){
            	// checking if the member is a constructor declaration. This was the only way I found to test that... [[[hemr]]]
            	if(owner.getIdent().equals(member.ident())){
            		member.check(context, 
            				super.isPrivate(),
            				JmlMessages.NON_PRIVATE_PURE_HELPER_CONSTRUCTOR);	
            	}
            	// otherwise is allowed
            }
            else{
            	member.check(context, 
        				super.isPrivate(),
        				JmlMessages.NON_PRIVATE_NON_PURE_HELPER);	
            }
        }

	member.check(context, 
		     !(hasFlag(modifiers(), ACC_NON_NULL) && hasFlag(modifiers(), ACC_NULLABLE)),
		     JmlMessages.NULLABLE_NON_NULL_TOGETHER);
    }

    /**
     * Check for illegal combinations of modifiers disallowed in 
     * interface method declarations.
     *
     * Adds the default public and abstract modifiers (not done for model 
     * methods);
     * these default modifiers are the only ones allowed for methods 
     * declared in interfaces. 
     *
     * @return	the new set of modifiers 
     */
    public long checkInterfaceMethodModifiers( CContextType context,
					      JMethodDeclaration member )
	throws PositionedError
    {
	if (owner().isInterface()) {
	    long modsBefore = modifiers;
            if (!isModel()) {
	        super.checkInterfaceMethodModifiers( context, member );
            } else { 
                // model methods may be static
                // Adds the public modifier, but not the abstract modifier
                modifiers |= ACC_PUBLIC;
                member.check( context,
                          !hasOtherFlags(stripNonJavaModifiers(modifiers),
                                  interfaceMethodModifiers | ACC_STATIC),
                          MjcMessages.METHOD_FLAGS_IN_INTERFACE,
                          member.ident() );
            }

	    // MJC interface method modifier checking adds public and 
	    // abstract modifiers to interface methods. The added abstract 
	    // modifier has to be removed for "model" methods.

	    if (isModel()) {
		if (!hasFlag(modsBefore, ACC_ABSTRACT)) {
		    removeAbstractModifier();
		}
	    }
	    member.check(context, 
			 !(hasFlag(modifiers(), ACC_NON_NULL) && hasFlag(modifiers(), ACC_NULLABLE)),
			 JmlMessages.NULLABLE_NON_NULL_TOGETHER);
	}
	return modifiers;
    }

    // ----------------------------------------------------------------------
    // PROTECTED STATIC DATA MEMBERS
    // ----------------------------------------------------------------------

    // the valid JML class modifiers are:
    //	ACC_SPEC_PUBLIC + ACC_SPEC_PROTECTED 
    //	+ ACC_MODEL + ACC_PURE + ACC_QUERY 
    //  + ACC_NON_NULL_BY_DEFAULT + ACC_NULLABLE_BY_DEFAULT;
    /**
     * The invalid JML class modifiers are ghost, instance, monitored, 
     * uninitialized, non_null, nullable, helper and extract.
     */
    protected static final long invalidJmlClassModifiers
	= ACC_GHOST + ACC_INSTANCE + ACC_MONITORED + ACC_UNINITIALIZED
	+ ACC_HELPER + ACC_NON_NULL + ACC_NULLABLE + ACC_EXTRACT;

    // the valid JML field modifiers are:
    //	ACC_SPEC_PUBLIC + ACC_SPEC_PROTECTED 
    //	+ ACC_MODEL + ACC_GHOST + ACC_INSTANCE + ACC_SECRET
    //	+ ACC_NON_NULL + ACC_NULLABLE + ACC_MONITORED + ACC_UNINITIALIZED;
    /**
     * The invalid JML field modifiers.
     */
    protected static final long invalidJmlFieldModifiers
	= ACC_PURE + ACC_HELPER + ACC_QUERY 
	+ ACC_NULLABLE_BY_DEFAULT
	+ ACC_NON_NULL_BY_DEFAULT
	+ ACC_EXTRACT;

    // the valid JML method modifiers are:
    //	ACC_SPEC_PUBLIC + ACC_SPEC_PROTECTED + ACC_EXTRACT
    //	+ ACC_MODEL + ACC_PURE + ACC_QUERY + ACC_SECRET 
    //  + ACC_NON_NULL + ACC_NULLABLE + ACC_HELPER;
    /**
     * The invalid JML method modifiers are ghost, instance, monitored, 
     * and uninitialized.
     */
    protected static final long invalidJmlMethodModifiers
	= ACC_GHOST + ACC_INSTANCE + ACC_MONITORED + ACC_UNINITIALIZED
	+ ACC_NULLABLE_BY_DEFAULT
	+ ACC_NON_NULL_BY_DEFAULT;
}
