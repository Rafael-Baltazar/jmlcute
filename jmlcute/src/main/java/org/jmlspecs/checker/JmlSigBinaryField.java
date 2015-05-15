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
 * $Id: JmlSigBinaryField.java,v 1.2 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlFieldInfo;
import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CBinaryField;
import org.multijava.mjc.CClass;

/**
 * A class to represent JML field declaratons read from bytecode
 * files.  
 *
 * @author Yoonsik
 */
public class JmlSigBinaryField extends CBinaryField implements JmlModifiable {

    // --------------------------------------------------------------------
    // CONSTRUCTOR
    // --------------------------------------------------------------------

    /** 
     * Creates a new instance by using the given field info
     * <code>fieldInfo</code>.
     */
    public JmlSigBinaryField(CClass owner, JmlFieldInfo fieldInfo) {
        super(createMemberAccess(owner, fieldInfo), fieldInfo);
    }

    /**
     * Returns true iff this field is explicitly declared as model.
     */
    public /*@ pure @*/ boolean isModel() {
	return ((JmlMemberAccess)access()).isModel();
    }

    /**
     * Returns true iff this field is explicitly declared as ghost.
     */
    public /*@ pure @*/ boolean isGhost() {
	return ((JmlMemberAccess)access()).isGhost();
    }

    /**
     * Returns true iff this field should be treated as a model field;
     * the field itself is defined as model (or ghost) or it is defined in a 
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
     * Creates a JML member access for the given JML field info object
     * <code>fieldInfo</code>.
     */
    private static JmlMemberAccess createMemberAccess(CClass owner, 
                                                      JmlFieldInfo fieldInfo) {
        short javaModifiers = fieldInfo.getModifiers();
        short jmlModifiers = fieldInfo.getJmlModifiers();
        return new JmlMemberAccess(owner, (long)(jmlModifiers << 16 | javaModifiers)&0xFFFFFFFFL);
    }
}
