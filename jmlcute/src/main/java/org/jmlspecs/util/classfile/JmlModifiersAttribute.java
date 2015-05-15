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
 * $Id: JmlModifiersAttribute.java,v 1.1 2003/11/14 21:58:20 cheon Exp $
 */

package org.jmlspecs.util.classfile;

import java.io.*;
import org.multijava.util.classfile.*;

/**
 * An attribute class to represent JML modifiers.
 *
 * @author Yoonsik Cheon
 */
public class JmlModifiersAttribute extends Attribute {

    // --------------------------------------------------------------------
    // CONSTRUCTORS
    // --------------------------------------------------------------------

    /** Creates a new instance.
     * 
     * @param modifiers the higher 16-bits (JML part) of the modifiers.
     * 
     * <pre><jml>
     *  requires modifiers >= 0;
     *  ensures thos.modifiers == modifiers;
     * </jml></pre>
     */
    public JmlModifiersAttribute(short modifiers) {
        this.modifiers = modifiers;
    }

    /**
     * Constructs a JML modifier attribute from a class file stream.
     */
    public JmlModifiersAttribute(DataInput in, ConstantPool cp)
	throws IOException, ClassFileFormatException {

	if (in.readInt() != 2) {
	    throw new ClassFileFormatException("Bad attribute length");
	}
	modifiers = in.readShort();
    }

    // --------------------------------------------------------------------
    // READ AND WRITE
    // --------------------------------------------------------------------

    /**
     * Inserts or checks location of constant value on constant pool.
     */
    protected void resolveConstants(ConstantPool cp) {
	cp.addItem(attr);
    }

    /**
     * Writes this attribute to the output <code>code</code>.
     */
    protected void write(ConstantPool cp, DataOutput out) throws IOException {
	out.writeShort(attr.getIndex());
	out.writeInt(2);
	out.writeShort(modifiers);
    }

    // --------------------------------------------------------------------
    // ACCESSORS
    // --------------------------------------------------------------------

    /**
     * Returns the tag of this attribute.
     *
     * <pre><jml>
     *  ensures \result == Constants.ATT_JML_MODIFIERS;
     * </jml></pre>
     */
    protected int getTag() {
	return Constants.ATT_JML_MODIFIERS;
    }

    /**
     * Returns the space in bytes used by this attribute in the classfile.
     *
     * <pre><jml>
     *  ensures \result == 8;
     * </jml></pre>
     */
    protected int getSize() {
	return 2 + 4 + 2;
    }

    public short jmlModifiers() {
        return modifiers;
    }

    // --------------------------------------------------------------------
    // DATA MEMBERS
    // --------------------------------------------------------------------

    /*@ spec_public @*/ private short modifiers;

    static final String tagString = "org.jmlspecs.modifiers";

    private static AsciiConstant attr = new AsciiConstant(tagString);
  
}
