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
 * $Id: JmlClassInfoCreator.java,v 1.2 2003/11/18 01:51:46 davidcok Exp $
 */

package org.jmlspecs.util.classfile;

import java.io.*;
import org.multijava.mjc.*;
import org.multijava.util.classfile.*;

/**
 * A concrete class info creator to create JML class info from
 * bytecode files.
 * 
 * @author Yoonsik Cheon
 */
public class JmlClassInfoCreator extends ClassInfoCreator {

    // --------------------------------------------------------------------
    // CONSTRUCTOR
    // --------------------------------------------------------------------

    /** 
     * Creates a new instance. This constructor is private to implement
     * the Singleton design pattern.
     */
    private JmlClassInfoCreator() {
    }

    // --------------------------------------------------------------------
    // CREATOR METHODS
    // --------------------------------------------------------------------
    
    /**
     * Creates a JML class info by reading bytecode from the data input
     * stream <code>name</code>.
     * 
     * <pre><jml>
     *  also ensures \result instanceof JmlClassInfo;
     * </jml></pre>
     */
    public /*@ non_null @*/ ClassInfo createClassInfo(
        /*@ non_null @*/ DataInput data, boolean interfaceOnly)
        throws IOException, ClassFileFormatException {

        return new JmlClassInfo(data);
    }

    /**
     * Creates a JML field info object by reading bytecode from the
     * data input stream <code>data</code>.
     */
    public /*@ non_null @*/ FieldInfo createFieldInfo(
        /*@ non_null @*/ DataInput data, /*@ non_null @*/ ConstantPool cp)
        throws IOException, ClassFileFormatException {

        return new JmlFieldInfo(data, cp);
    }

    /**
     * Creates a JML method info object by reading bytecode from the
     * data input stream <code>data</code>.
     */
    public /*@ non_null @*/ MethodInfo createMethodInfo(
        /*@ non_null @*/ DataInput data, /*@ non_null @*/ ConstantPool cp,
        boolean interfaceOnly)
        throws IOException, ClassFileFormatException {

        return new JmlMethodInfo(data, cp, interfaceOnly);
    }

    // --------------------------------------------------------------------
    // SINGLETON METHOD
    // --------------------------------------------------------------------

    /** Returns the unique intance of this class. */
    public static /*@ non_null @*/ ClassInfoCreator getInstance() {
        return theInstance;
    }

    // --------------------------------------------------------------------
    // DATA MEMBERS
    // --------------------------------------------------------------------

    /** The unique instance of this class. */
    private static final /*@ non_null @*/ JmlClassInfoCreator theInstance 
        = new JmlClassInfoCreator();
}
