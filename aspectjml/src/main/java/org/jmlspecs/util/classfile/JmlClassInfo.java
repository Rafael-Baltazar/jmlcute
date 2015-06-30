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
 * $Id: JmlClassInfo.java,v 1.4 2005/04/26 02:40:35 kui_dai Exp $
 */

package org.jmlspecs.util.classfile;

import java.io.*;
import org.multijava.util.classfile.*;

/**
 * A class to represent JML symbol files. The strucure of JML symbol files
 * is similar to that of Java class files.
 * 
 * @author Yoonsik Cheon
 */
public class JmlClassInfo extends ClassInfo {

    /**
     * Creates a JML class info object.
     */
    public JmlClassInfo(long modifiers,
                        String thisClass,
                        String superClass,
                        ClassConstant[] interfaces,
                        FieldInfo[] fields,
                        MethodInfo[] methods,
                        InnerClassInfo[] innerClasses,
                        AttributeList attributes,
                        File sourceFile,
                        boolean deprecated) {
        super((short)modifiers, thisClass, superClass,null, interfaces, fields,
              methods, innerClasses, attributes, sourceFile, deprecated);
        addJmlModifiers(modifiers);
    }
    
    /**
     * Creates a JML class info object from the bytecode stream
     * <code>in</code>.
     */
    public JmlClassInfo(/*@ non_null @*/ DataInput in) 
        throws IOException, ClassFileFormatException {
        super(in, true, JmlClassInfoCreator.getInstance());
    }

    /**
     * Returns the JML modifiers.
     */
    public short getJmlModifiers() {
        if (modifiers != -1) {
            return modifiers;
        }

        Attribute attr = attributes.get(Constants.ATT_JML_MODIFIERS);
        modifiers = (short)
            (attr == null ? 0 : ((JmlModifiersAttribute)attr).jmlModifiers());
        return modifiers;
    }


    /** 
     * Creates an output file. This method is overridden here to creat
     * an output file whose suffix is ".sym".
     */
    protected File createOutputFile(File dir, String className) {
        return new File(dir, className + ".sym");
    }

    // --------------------------------------------------------------------
    // HELPERS
    // --------------------------------------------------------------------

    /**
     * Adds the JML part of the given modifiers, <code>modifiers</code>,
     * to the attribute list of this class info.
     */
    private void addJmlModifiers(long modifiers) {
        this.modifiers = (short) (modifiers >>> 16);
        if (this.modifiers != 0) {
            attributes.add(new JmlModifiersAttribute(this.modifiers));
        }
    }

    // --------------------------------------------------------------------
    // DATA MEMBERS
    // --------------------------------------------------------------------

    /** 
     * Cached JML modifiers. If the value is -1, it means the value is
     * not initialized yet. 
     */
    private short modifiers = -1;
}
