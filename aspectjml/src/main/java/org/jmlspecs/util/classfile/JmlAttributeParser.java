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
 * $Id: JmlAttributeParser.java,v 1.1 2003/11/14 21:58:20 cheon Exp $
 */

package org.jmlspecs.util.classfile;

import java.io.*;
import org.multijava.mjc.*;
import org.multijava.util.classfile.*;

/**
 * A class to implement JML-specific attribute parser. This class parses
 * JML-specific attributes from bytecode streams.
 *
 * @author Yoonsik Cheon
 */
public class JmlAttributeParser implements AttributeParser {

    /**
     * Checks the next attribute in the given data input,
     * <code>in</code>, and parses it if it is recognized.
     */
    public Attribute read(String tag, DataInput in, ConstantPool cp)
	throws IOException, ClassFileFormatException {

	if (!isOurs(tag)) {
	    return null;
	}
	
	switch (tag.charAt(firstInterestingPos)) {
	case 'm':		
	    if (tag.equals(JmlModifiersAttribute.tagString)) {
		return new JmlModifiersAttribute(in, cp);
	    }
	    break;

	default:
	    break;
	}

	return null;
    }

    /**
     * Checks the next attribute in the given data input,
     * <code>in</code>, and parses it if it is recognized.
     */
    public Attribute readInterfaceOnly(String tag, DataInput in, 
                                       ConstantPool cp)
	throws IOException, ClassFileFormatException {

        return read(tag, in, cp);
    }

    /**
     * Checks the next attribute in the given data input,
     * <code>in</code>, and parses it if it is recognized.
     */
    public Attribute readCodeInfoAttribute(String tag, DataInput in, 
                                           ConstantPool cp,
                                           Instruction[] insns)
	throws IOException, ClassFileFormatException {

        return read(tag, in, cp);
    }

    // -------------------------------------------------------------
    // HELPERS
    // -------------------------------------------------------------

    /**
     * Returns true if the attribute named by the given tag string is
     * an attribute of <code>org.jmlspecs.</code>  
     */
    private boolean isOurs(String tag) {
	return tag.startsWith(tagPrefix);
    }

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

    private static final String tagPrefix = "org.jmlspecs.";
    private static final int firstInterestingPos = tagPrefix.length();
}
