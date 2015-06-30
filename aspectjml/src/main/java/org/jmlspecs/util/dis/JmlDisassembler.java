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
 * $Id: JmlDisassembler.java,v 1.3 2005/04/26 02:40:38 kui_dai Exp $
 */

package org.jmlspecs.util.dis;

import java.io.*;

import org.jmlspecs.util.classfile.*;
import org.multijava.dis.*;
import org.multijava.util.classfile.*;
import org.multijava.util.compiler.UnpositionedError;

/**
 * A class to print type signatures encoded in .sym files. The .sym
 * file is an extension to Java .class file but without the bytecode
 * for method bodies.
 */
public class JmlDisassembler extends org.multijava.dis.Disassembler
    implements Constants {

    // --------------------------------------------------------------------
    // CONSTRUCTORS
    // --------------------------------------------------------------------

    /**
     * Creates a disassembler object for the given class info
     * <code>classInfo</code>.
     */
    private JmlDisassembler(JmlClassInfo classInfo, JDisOptions options) {
        super(classInfo, options);
    }

    // --------------------------------------------------------------------
    // PRINTING AND OVERRIDDEN METHODS
    // --------------------------------------------------------------------

    /** Disassembles a symbol file. */
    public static void disassemble(
        String sourceFile, String destination, DisOptions options) 
	throws UnpositionedError {
        Disassembler.disassemble(sourceFile, destination, options, helper);
    }

    /** 
     * Prints the modifiers of the given class info. This method is
     * overridden here to also write JML-specific modifiers.
     */
    protected void writeModifiers(IndentingWriter out, ClassInfo info) {
        int modifiers = ((JmlClassInfo)info).getJmlModifiers();
        modifiers = modifiers << 16 | info.getModifiers();
        writeModifiers(out, modifiers & ~ACC_SUPER);
    }

    /** 
     * Prints the modifiers of the given inner class info. This method
     * is overridden here to also write JML-specific modifiers.
     */
    protected void writeModifiers(IndentingWriter out, InnerClassInfo info) {
        // !FIXME!
        writeModifiers(out, info.getModifiers());
    }

    /** 
     * Prints the modifiers of the given field info. This method
     * is overridden here to also write JML-specific modifiers.
     */
    protected void writeModifiers(IndentingWriter out, FieldInfo info) {
        int modifiers = ((JmlFieldInfo)info).getJmlModifiers();
        modifiers = modifiers << 16 | info.getModifiers();
        writeModifiers(out, modifiers);
    }

    /** 
     * Prints the modifiers of the given method info. This method
     * is overridden here to also write JML-specific modifiers.
     */
    protected void writeModifiers(IndentingWriter out, MethodInfo info) {
        int modifiers = ((JmlMethodInfo)info).getJmlModifiers();
        modifiers = modifiers << 16 | info.getModifiers();
        writeModifiers(out, modifiers);
    }

    /** 
     * Prints the given modifiers that may contain both JML and Java
     * modifiers.
     */
    private void writeModifiers(IndentingWriter out, long modifiers) {
        if ((modifiers & ACC_SPEC_PUBLIC) != 0) {
	    out.print("spec_public ");
        } else if ((modifiers & ACC_SPEC_PROTECTED) != 0) {
	    out.print("spec_protected ");
        }

	if ((modifiers & ACC_PUBLIC) != 0) {
	    out.print("public ");
	} else if ((modifiers & ACC_PROTECTED) != 0) {
	    out.print("protected ");
	} else if ((modifiers & ACC_PRIVATE) != 0) {
	    out.print("private ");
	}

	if ((modifiers & ACC_STATIC) != 0) {
	    out.print("static ");
	} else if ((modifiers & ACC_INSTANCE) != 0) {
	    out.print("instance ");
        }

	if ((modifiers & ACC_ABSTRACT) != 0) {
	    out.print("abstract ");
	}
	if ((modifiers & ACC_FINAL) != 0) {
	    out.print("final ");
	}

	if ((modifiers & ACC_MODEL) != 0) {
	    out.print("model ");
	} else if ((modifiers & ACC_GHOST) != 0) {
	    out.print("ghost ");
	}
	if ((modifiers & ACC_HELPER) != 0) {
	    out.print("helper ");
	}
	if ((modifiers & ACC_NATIVE) != 0) {
	    out.print("native ");
	}
	if ((modifiers & ACC_SYNCHRONIZED) != 0) {
	    out.print("synchronized ");
	}
	if ((modifiers & ACC_MONITORED) != 0) {
	    out.print("monitored ");
	}
	if ((modifiers & ACC_TRANSIENT) != 0) {
	    out.print("transient ");
	}
	if ((modifiers & ACC_VOLATILE) != 0) {
	    out.print("volatile ");
	}
	if ((modifiers & ACC_PURE) != 0) {
	    out.print("pure ");
	}
	if ((modifiers & ACC_NON_NULL) != 0) {
	    out.print("non_null ");
	}
	if ((modifiers & ACC_UNINITIALIZED) != 0) {
	    out.print("uninitialized ");
	}
    }

    // ----------------------------------------------------------------------
    // INNER CLASSES
    // ----------------------------------------------------------------------
    
    /**
     * A helper class to tune the disassembler to JML.
     */
    protected static class JmlDisassemblerHelper 
        extends org.multijava.dis.Disassembler.DisassemblerHelper {

        /**
         * Returns the file name extension for symbol files.
         */
        public /*@ non_null @*/ String inputExtension() {
            return ".sym";
        }

        /**
         * Returns the file name extension for disassembled files.
         */
        public /*@ non_null @*/ String outputExtension() {
            return ".dsm";
        }

        /**
         * Returns a disassembler for the given class info.
         */
        public /*@ non_null @*/ Disassembler createDisassembler(
            ClassInfo classInfo, DisOptions options) {
            return new JmlDisassembler(
                (JmlClassInfo)classInfo, (JDisOptions)options);
        }

        /**
         * Creates a class info by reading bytecode from the given
         * data stream.
         */
        public /*@ non_null @*/ ClassInfo createClassInfo(DataInput in) 
            throws IOException, ClassFileFormatException {
            return new JmlClassInfo(in);
        }

        /**
         * Create a class info by reading byrecode from the file whose
         * name is given as the argument <code>name</code>.
         */
        public /*@ non_null @*/ ClassInfo createClassInfo(String name) 
	    throws ClassFileReadException
	{
            return ClassPath.getClassInfo(
                name, ".sym", JmlClassInfoCreator.getInstance(), false, true);
        }
    }

    // --------------------------------------------------------------------
    // DATA MEMBERS
    // --------------------------------------------------------------------

    /**
     * A helper object to tune the disassembler to JML.
     */
    private static final /*@ non_null @*/ JmlDisassemblerHelper helper = 
        new JmlDisassemblerHelper();
}
