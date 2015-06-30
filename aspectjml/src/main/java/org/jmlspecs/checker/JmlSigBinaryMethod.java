/*
 * Copyright (C) 2003 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: JmlSigBinaryMethod.java,v 1.3 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlMethodInfo;
import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CBinaryMethod;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CType;

/**
 * A class to represent JML method declaratons read from bytecode
 * files.  
 *
 * @author Yoonsik
 */
public class JmlSigBinaryMethod extends CBinaryMethod 
    implements JmlModifiable, org.jmlspecs.checker.Constants {

    // --------------------------------------------------------------------
    // CONSTRUCTOR
    // --------------------------------------------------------------------

    /** 
     * Creates a new instance by using the given method info
     * <code>methodInfo</code>.
     */
    public JmlSigBinaryMethod(CClass owner, JmlMethodInfo methodInfo,
                              CContextType declarationContext) {
        super(createMemberAccess(owner, methodInfo), methodInfo,
              declarationContext);
    }

    /**
     * Returns true iff this method is explicitly declared as model.
     */
    public /*@ pure @*/ boolean isModel() {
	return ((JmlMemberAccess)access()).isModel();
    }

    /**
     * Returns true iff this method is explicitly declared as ghost.
     */
    public /*@ pure @*/ boolean isGhost() {
	return ((JmlMemberAccess)access()).isGhost();
    }

    /**
     * Returns true iff this field should be treated as a model method;
     * the method itself is defined as model (or ghost) or it is defined in a 
     * model class or interface.
     */
    public /*@ pure @*/ boolean isEffectivelyModel() {
        JmlMemberAccess acc = (JmlMemberAccess) access();
	return acc.isModel()
	    || acc.isGhost()
	    || (owner() != null 
		&& ((JmlModifiable)owner()).isEffectivelyModel());
    }

    /**
     * Returns true if this method is applicable to a method call with
     * the given identifier and actual (static) argument types. This method
     * refines the inherited method to make model methods applicable only 
     * in specfication contexts (i.e., in spec scope).
     *
     * @param ident the identifier to match
     * @param recvType receiver type	
     * @param actuals the method call static argument types
     * @return true if this method is applicable 
     * @see CMethod#isApplicable(String, CType, CType[])
     */
    public boolean isApplicable(String ident, CType recvType,
                                CType[] actuals) {
	boolean result = super.isApplicable(ident, recvType, actuals,
					    CClassType.EMPTY);
        
	// model methods are visible only in spec scope
	if (result && isEffectivelyModel()) {
	    result = JmlContext.inSpecScope();
	}
	return result;
    }

    /**
     * Returns true if this member is public, including spec_public
     * in a JML specification scope.
     * @see #isProtected()
     * @see #isPrivate()
     */
    public /*@ pure @*/ boolean isPublic() {
	return ((JmlMemberAccess)access()).isPublic();
    }

    /**
     * Returns true if this member is protected, including spec_protected
     * in a JML specification scope.
     * @see #isPublic()
     * @see #isPrivate()
     */
    public /*@ pure @*/ boolean isProtected() {
	return ((JmlMemberAccess)access()).isProtected();
    }

    /**
     * Returns true if this member is private. In a JML specification
     * scope, it also means not being spec_public nor spec_protected.
     * @see #isProtected()
     * @see #isPublic()
     */
    public /*@ pure @*/ boolean isPrivate() {
	return ((JmlMemberAccess)access()).isPrivate();
    }

    /** Returns true if this method is spec_public. */
    public /*@ pure @*/ boolean isSpecPublic() {
	return ((JmlMemberAccess)access()).isSpecPublic();
    }

    /** Returns true if this method is spec_protected. */
    public /*@ pure @*/ boolean isSpecProtected() {
	return ((JmlMemberAccess)access()).isSpecProtected();
    }

    /**
     * Returns true if this method is pure. A method is pure if it is
     * annotated with the JML <code>pure</code> modifier or it
     * inherits pureness from its owner or supertypes. A non-static
     * method (including a constructor) is pure if its owner class or
     * interface is pure, or if it overrides a pure method inherited
     * from supertypes (classes and intefaces).
     */
    public boolean isPure() {
        return ((JmlMemberAccess)access()).isPure();
    }

    /**
     * Creates a JML member access for the given JML method info object
     * <code>methodInfo</code>.
     */
    private static JmlMemberAccess createMemberAccess(
        CClass owner, JmlMethodInfo methodInfo) {
        short javaModifiers = methodInfo.getModifiers();
        short jmlModifiers = methodInfo.getJmlModifiers();
        return new JmlMemberAccess(owner, (long)(jmlModifiers << 16 | javaModifiers)&0xFFFFFFFFL);
    }
}
