/*
 * Copyright (C) 2001 Iowa State University
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
 * $Id: RacParser.java,v 1.7 2006/12/11 05:59:03 chalin Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.*;
import org.multijava.mjc.*;

import java.util.*;
import java.io.*;

/**
 * A utility class for generating RAC nodes from a string and an array of 
 * RAC/JML nodes. This class provides several inner classes implementing
 * RAC nodes and provides a set of factory methods for creating them.
 *
 * @see RacNode
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.7 $
 */

public abstract class RacParser {


    // ----------------------------------------------------------------------
    // FACTORY METHODS
    // ----------------------------------------------------------------------

    /** Returns an object of <code>RacMethodDeclaration</code> for the
     * given string. The string is treated as a method declaration.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacMethodDeclaration parseMethod(String code)
    {
	Object asts[] = { };
	return parseMethod(code, asts);
    }

    /** Returns an object of <code>RacMethodDeclaration</code> for the
     * given string. The string is treated as a method declaration and
     * may contain a marker ($0) at which position the object 
     * <code>ast</code> is inserted.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacMethodDeclaration parseMethod(String code, Object ast)
    {
	Object asts[] = { ast };
	return parseMethod(code, asts);
    }

    /** Returns an object of <code>RacMethodDeclaration</code> for the
     * given string. The string is treated as a method declaration and
     * may contain markers ($0, $1) at which positions the objects 
     * <code>ast1</code> and <code>ast2</code> are inserted repectively.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacMethodDeclaration parseMethod(String code, Object ast1,
						   Object ast2)
    {
	Object asts[] = { ast1, ast2 };
	return parseMethod(code, asts);
    }

    /** Returns an object of <code>RacMethodDeclaration</code> for the
     * given string. The string is treated as a method declaration and
     * may contain markers ($0, $1, $2) at which positions the objects 
     * <code>ast1</code>, <code>ast2</code>, and <code>ast3</code> are 
     * inserted repectively.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacMethodDeclaration parseMethod(String code, Object ast1,
						   Object ast2, Object ast3)
    {
	Object asts[] = { ast1, ast2, ast3 };
	return parseMethod(code, asts);
    }

    /** Returns an object of <code>RacMethodDeclaration</code> for the
     * given string. The string is treated as a method declaration and
     * may contain markers ($i) at which positions the i-th object
     * of the array <code>asts</code> is inserted.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacMethodDeclaration parseMethod(String code, Object asts[])
    {
	return new RacMethodDeclaration(parse(code, asts));
    }

    /** Returns an object of <code>RacStatement</code> for the
     * given string. The string is treated as a statement and
     * may contain a marker ($0) at which position the object 
     * <code>ast</code> is inserted.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacStatement parseStatement(String code, Object ast)
    {
	Object asts[] = { ast };
	return parseStatement(code, asts);
    }

    /** Returns an object of <code>RacStatement</code> for the
     * given string. The string is treated as a statement and
     * may contain markers ($0, $1) at which positions the objects 
     * <code>ast1</code> and <code>ast2</code> are inserted repectively.
     * For example, the following call creates a <code>RacStatement</code>
     * object representing an <code>if</code>-statement.
     *
     * <pre>
     * parseStatement("if (x > 1) { $0 } else { $1 }", s1, s2);
     * </pre>
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacStatement parseStatement(String code,
					      Object ast1, Object ast2)
    {
	Object asts[] = { ast1, ast2 };
	return parseStatement(code, asts);
    }

    /** Returns an object of <code>RacStatement</code> for the
     * given string. The string is treated as a statement and
     * may contain markers ($0, $1, $2) at which positions the objects 
     * <code>ast1</code>, <code>ast2</code>, and <code>ast3</code> are 
     * inserted repectively.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacStatement parseStatement(
      String code, Object ast1, Object ast2, Object ast3) 
    {
	Object asts[] = { ast1, ast2, ast3 };
	return parseStatement(code, asts);
    }

    /** Returns an object of <code>RacStatement</code> for the
     * given string. The string is treated as a statement.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacStatement parseStatement(String code)
    {
	Object asts[] = {};
	return parseStatement(code, asts);
    }


    /** Returns an object of <code>RacStatement</code> for the
     * given string. The string is treated as a statement and
     * may contain markers ($i) at which positions the i-th object
     * of the array <code>asts</code> is inserted.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacStatement parseStatement(String code, Object asts[])
    {
	return new RacStatement(parse(code, asts));
    }

    /** Returns an object of <code>RacBlock</code> for the
     * given string. The string is treated as a block statement.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacBlock parseBlock(String code)
    {
	Object asts[] = {};
	return new RacBlock(parse(code, asts));
    }

    /** Returns an object of <code>RacBlock</code> for the
     * given string. The string is treated as a block statement and
     * may contain a marker ($0) at which position the object 
     * <code>ast</code> is inserted.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacBlock parseBlock(String code, Object ast)
    {
	Object asts[] = { ast };
	return new RacBlock(parse(code, asts));
    }

    /** Returns an object of <code>RacBlock</code> for the given
     * string. The string is treated as a block statement and may
     * contain two markers $0 and $1 and at which position the object
     * <code>ast1</code>, and <code>ast2</code> are inserted
     * respectively.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacBlock parseBlock(String code, Object ast1, Object ast2)
    {
	Object asts[] = { ast1, ast2 };
	return new RacBlock(parse(code, asts));
    }

    /** Returns an object of <code>RacBlock</code> for the given
     * string. The string is treated as a block statement and may
     * contain three markers $0, $1, and $2 and at which position the
     * object <code>ast1</code>, <code>ast2</code>, and
     * <code>ast3</code> are inserted respectively.
     *
     * <pre><jml>
     * requires code != null;
     * </jml></pre>
     */
    public static RacBlock parseBlock(String code, Object ast1, 
                                      Object ast2, Object ast3)
    {
	Object asts[] = { ast1, ast2, ast3 };
	return new RacBlock(parse(code, asts));
    }

    /** Parses the given string representing verbatim code possibly 
     * with positional markers ($i) and returns a list of objects
     * (strings, objects, END_OF_LINE's) with $i replaced by the i-th
     * objects of the array <code>asts</code>. For example, if code is
     *
     * <pre>
     *  "if ($0) {\n  count = count + 1;\n}"
     * </pre>
     *
     * then, the returnes list is has the following form:
     * 
     * <pre>
     *  "if ("
     *  arg0
     *  ") {"
     *  END_OF_LINE
     *  "  count = count + 1;"
     *  END_OF_LINE
     *  "}"
     * </pre>
     *
     * <pre><jml>
     * requires code != null;
     * ensures \result != null;
     * </jml></pre>     
     */
    private static List parse(String code, Object asts[])
    {
	List pieces = new ArrayList();
	Reader rd = new StringReader(code);
	StringBuffer buf = new StringBuffer();
	try {
	    int c = rd.read();
	    while (c != -1) {
		if (c == '$') {
		    c = rd.read();
		    int n = -1;
		    while (c >= '0' && c <= '9') {
			n = (n > 0 ? n : 0) * 10 + (c - '0');
			c = rd.read();
		    }
		    if (n >= 0) {
			if (buf.length() > 0) {
			    pieces.add(buf.toString());
			    buf = new StringBuffer();
			}
			//[[[hemr]]]
			if(asts != null){
				if (n < asts.length)
				    pieces.add(asts[n]);
				else
				    throw new IllegalArgumentException(
				      "No argument at position "+ n +"($"+ n +")");
			}
		    } else
			buf.append("$"); 
		} else if (c == '\n') {
		    if (buf.length() > 0) {
			pieces.add(buf.toString());
			buf = new StringBuffer();
		    }
		    pieces.add(END_OF_LINE);
		    c = rd.read();
		} else {
		    buf.append((char)c);
		    c = rd.read();
		}
	    } // while (c != -1)
	}
	catch (IOException e) {
	    throw new IllegalArgumentException(e.getMessage());
	}
	
	if (buf.length() > 0) {
	    pieces.add(buf.toString());
	}
	
	return pieces;
    }

    // ----------------------------------------------------------------------
    // HIDDEN INNER CLASSES
    // ----------------------------------------------------------------------

    /** A RAC node class for representing statements. A RAC statement is 
     * represented verbatim as a sequence of lines, where a line can be
     * a string, an END_OF_LINE marker, and an object representing other
     * RAC/JML node.
     */
    public static class RacStatement extends JStatement implements RacNode
    {
        /** Creates a new instance.
         *
         * <pre><jml>
         * requires pieces != null;
         * </jml></pre>
        */
	private RacStatement(List pieces) {
	    super(org.multijava.util.compiler.TokenReference.NO_REF, null);
	    this.pieces = pieces;
	    this.indent = 0;
	}

	public int indent() {
	    return indent;
	}

	public RacNode incrIndent() {
	    ++indent;
	    return this;
	}

	public Iterator iterator() {
	    return pieces.iterator();
	}

	public void genCode(CodeSequence code) {
	    throw new UnsupportedOperationException();
	}

	public void typecheck(CFlowControlContextType context) {
	    throw new UnsupportedOperationException();
	}

	/**
	 * Accepts the specified visitor.
	 * @param p the visitor 
	 */
	public void accept( MjcVisitor p ) {
	    if (p instanceof RacVisitor)
		((RacVisitor)p).visitRacNode( this );
	    else
		throw new UnsupportedOperationException(
		  "Can't visit a RAC AST with an MjcVisitor");
	}
	
	public String name() {
	    return name;
	}
	
	public void setName(String name) {
	    this.name = name;
	}

        /** Sets the variable declaration to be piggyback with this code.
         * 
         * @see #varDecl()
         */
        public void setVarDecl(PreValueVars.Entry varDecl) {
            this.varDecl = varDecl;
        }
    
        /** Returns the variable declaration associated with this
         * code. This method is used to piggyback a variable declaration
         * with this code.
         * 
         * @see #setVarDecl(PreValueVars.Entry)
         */
        public PreValueVars.Entry varDecl() {
            return varDecl;
        }

        /** The variable declaration to be piggyback with this code. */
        private PreValueVars.Entry varDecl;

        /** Name of this statement node. */
	private String name;

        /** The list of elements constituting this statement node. */
	private /*@ non_null @*/ List pieces;

        /** Indentation level of this statement node. */
	private int indent;
    }

    /** A RAC node class for representing method declarations. A RAC 
     * method declaration is represented verbatim as a sequence of lines, 
     * where a line can be a string, an END_OF_LINE marker, and an object
     * representing other RAC/JML node.
     */
    public static class RacMethodDeclaration extends JmlMethodDeclaration
	implements JMethodDeclarationType, RacNode
    {
        /** Creates a new instance.
         *
         * <pre><jml>
         * requires pieces != null;
         * </jml></pre>
        */
	private RacMethodDeclaration(List pieces) {
	    super(org.multijava.util.compiler.TokenReference.NO_REF, null, null);
	    this.pieces = pieces;
	    this.indent = 0;
	}

	public int indent() {
	    return indent;
	}

	public RacNode incrIndent() {
	    ++indent;
	    return this;
	}

	public Iterator iterator() {
	    return pieces.iterator();
	}

	/**
	 * Accepts the specified visitor.
	 * @param p the visitor 
	 */
	public void accept( MjcVisitor p ) {
	    if (p instanceof RacVisitor)
		((RacVisitor)p).visitRacNode( this );
	    else
		throw new UnsupportedOperationException(
		  "Cannot visit a RAC AST with an MjcVisitor");
	}
	public String name() {
	    return name;
	}
	
	public void setName(String name) {
	    this.name = name;
	}

        /** Sets the variable declaration to be piggyback with this code.
         * 
         * @see #varDecl()
         */
        public void setVarDecl(PreValueVars.Entry varDecl) {
            this.varDecl = varDecl;
        }
    
        /** Returns the variable declaration associated with this
         * code. This method is used to piggyback a variable declaration
         * with this code.
         * 
         * @see #setVarDecl(PreValueVars.Entry)
         */
        public PreValueVars.Entry varDecl() {
            return varDecl;
        }

        /** The variable declaration to be piggyback with this code. */
        private PreValueVars.Entry varDecl;

        /** Name of this statement node. */
	private String name;

        /** The list of elements constituting this statement node. */
	private /*@ non_null @*/ List pieces;

        /** Indentation level of this statement node. */
	private int indent;
    }

    /** A RAC node class for representing blocks. A RAC block is represented
     * verbatim as a sequence of lines, where a line can be a string, 
     * an END_OF_LINE marker, and an object representing other RAC/JML node.
     */
    public static class RacBlock extends JBlock
	implements RacNode
    {
        /** Creates a new instance.
         *
         * <pre><jml>
         * requires pieces != null;
         * </jml></pre>
        */
	private RacBlock(List pieces) {
	    super(org.multijava.util.compiler.TokenReference.NO_REF, null, null);
	    this.pieces = pieces;
	    this.indent = 0;
	}

	public int indent() {
	    return indent;
	}

	public RacNode incrIndent() {
	    ++indent;
	    return this;
	}

	public Iterator iterator() {
	    return pieces.iterator();
	}

	/**
	 * Accepts the specified visitor.
	 * @param p the visitor 
	 */
	public void accept( MjcVisitor p ) {
	    if (p instanceof RacVisitor)
		((RacVisitor)p).visitRacNode( this );
	    else
		throw new UnsupportedOperationException(
		  "Cannot visit a RAC AST with an MjcVisitor");
	}
	public String name() {
	    return name;
	}
	
	public void setName(String name) {
	    this.name = name;
	}

        /** Sets the variable declaration to be piggyback with this code.
         * 
         * @see #varDecl()
         */
        public void setVarDecl(PreValueVars.Entry varDecl) {
            this.varDecl = varDecl;
        }
    
        /** Returns the variable declaration associated with this
         * code. This method is used to piggyback a variable declaration
         * with this code.
         * 
         * @see #setVarDecl(PreValueVars.Entry)
         */
        public PreValueVars.Entry varDecl() {
            return varDecl;
        }

        /** The variable declaration to be piggyback with this code. */
        private PreValueVars.Entry varDecl;

        /** Name of this block node. */
	private String name;

        /** The list of elements constituting this block node. */
	private /*@ non_null @*/ List pieces;

        /** Indentation level of this block node. */
	private int indent;
    }


    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** A marker object denoting the end of line. */
    public static final /*@ non_null @*/ Object END_OF_LINE = new Object();

}

