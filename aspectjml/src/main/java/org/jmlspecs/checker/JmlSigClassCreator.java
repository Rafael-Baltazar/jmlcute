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
 * $Id: JmlSigClassCreator.java,v 1.2 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlClassInfo;
import org.jmlspecs.util.classfile.JmlFieldInfo;
import org.jmlspecs.util.classfile.JmlMethodInfo;
import org.multijava.mjc.CBinaryField;
import org.multijava.mjc.CBinaryMethod;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.ClassCreator;
import org.multijava.mjc.MemberAccess;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.FieldInfo;
import org.multijava.util.classfile.MethodInfo;

/**
 * A concrete class creator to create JML classes from bytecode files.
 * 
 * @author Yoonsik Cheon
 */
public class JmlSigClassCreator extends ClassCreator {

    // --------------------------------------------------------------------
    // CONSTRUCTOR
    // --------------------------------------------------------------------

    /** 
     * Creates a new instance. This constructor is private to implement
     * the Singleton design pattern.
     */
    private JmlSigClassCreator() {
    }

    // --------------------------------------------------------------------
    // CREATOR METHODS
    // --------------------------------------------------------------------
    
    /**
     * Creates a JML binary field object. 
     */
    public /*@ non_null @*/ CBinaryField createBinaryField(
        /*@ non_null @*/ CClass owner, /*@ non_null @*/ FieldInfo fieldInfo) {
        return new JmlSigBinaryField(owner, (JmlFieldInfo) fieldInfo);
    }

    /**
     * Creates a JML binary method object. 
     */
    public /*@ non_null @*/ CBinaryMethod createBinaryMethod(
        CClass owner, MethodInfo methodInfo, CClassContextType declCtx) {
        return new JmlSigBinaryMethod(owner, (JmlMethodInfo) methodInfo, 
                                      declCtx);
    }

    /**
     * Creates a JML member access object.
     */
    public /*@ non_null @*/ MemberAccess createMemberAccess(
        CClass owner, CMemberHost host, ClassInfo classInfo) {
        short javaModifiers = classInfo.getModifiers();
        short jmlModifiers = ((JmlClassInfo)classInfo).getJmlModifiers();
        return new JmlMemberAccess(owner, 
                                   host, 
                                   (long)(jmlModifiers << 16 | javaModifiers)&0xFFFFFFFFL);
    }

    // --------------------------------------------------------------------
    // SINGLETON METHOD
    // --------------------------------------------------------------------

    /** Returns the unique intance of this class. */
    public static /*@ non_null @*/ ClassCreator getInstance() {
        return theInstance;
    }

    // --------------------------------------------------------------------
    // DATA MEMBERS
    // --------------------------------------------------------------------

    /** The unique instance of this class. */
    private static final /*@ non_null @*/ JmlSigClassCreator theInstance 
        = new JmlSigClassCreator();
}
