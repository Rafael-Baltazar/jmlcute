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
 * $Id: Main.java,v 1.2 2004/01/15 05:50:21 cclifton Exp $
 */

package org.jmlspecs.util.dis;

import org.jmlspecs.util.classfile.JmlAttributeParser;
import org.multijava.util.classfile.AttributeList;
import org.multijava.util.compiler.UnpositionedError;

/**
 * A class to print type signatures encoded in .sym files. The .sym
 * file is an extension to the Java .class file but without the
 * bytecode for method bodies.
 *
 * @author Yoonsik Cheon
 */
public class Main extends org.multijava.dis.Main {

    // --------------------------------------------------------------------
    // CONSTRUCTORS
    // --------------------------------------------------------------------

    /**
     * Creates a new instance.
     */
    private Main(String[] args) {
	super(args);
    }

    static {
        AttributeList.addParser(new JmlAttributeParser());
    }

    // --------------------------------------------------------------------
    // OVERRIDDEN HOOK METHODS
    // --------------------------------------------------------------------

    /*
     * Parses command line arguments.
     */
    protected boolean parseArguments(String[] args) {
            options = new JDisOptions();
	return options.parseCommandLine(args);
    }

    /**
     * Reads and disassembles the given symbol file.
     */
    protected void disassembleClass(String fileName) throws UnpositionedError {
	JmlDisassembler.disassemble(
            fileName, options.destination(), (JDisOptions) options);
    }

    // --------------------------------------------------------------------
    // ENTRY POINT
    // --------------------------------------------------------------------

    /** Disassemble a symbole file. */
    public static void main(String[] args) {
        boolean success = false;
        try {
            success = compile(args);
        } catch (Exception e) {
        }
	System.exit(success ? 0 : 1);
    }

    /** Disassemble a symbole file. */
    public static boolean compile(String[] args) {
	return new Main(args).disasm();
    }

    /** Disassemble a symbole file. */
    public static boolean run(String[] args) {
	return new Main(args).disasm();
    }
}
