/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id: JmlClassOrGFImport.java,v 1.11 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.FileFinder;
import org.multijava.mjc.JClassOrGFImport;
import org.multijava.mjc.JClassOrGFImportType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This type represents (in the AST) import statements for single
 * classes or generic functions, e.g., <code>import
 * java.util.ArrayList;</code> or <code>import
 * org.multijava.samples.typecheck</code>. */
public class JmlClassOrGFImport extends JmlNode implements JClassOrGFImportType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs an AST node for a class or external member import statement.
     * @param where	the token reference of this node
     * @param name	the class or external member name
     * @param comments	the non-javadoc comments for this statement
     * @param isModel	indicates whether this is a model import
     */
    public JmlClassOrGFImport( /*@ non_null */ TokenReference where, 
			       /*@non_null@*/ String name, 
			       /*@nullable@*/ JavaStyleComment[] comments,
			       boolean isModel ) {
	super(where);		// cached
	this.delegee = new JClassOrGFImport( where, name, comments );
	this.isModel = isModel;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS & MUTATORS
    // ----------------------------------------------------------------------

    /**
     * @return the class name defined by this statement
     */
    public /*@non_null@*/ String getName()
    {
	return delegee.getName();
    }

    /**
     * @return the class name defined by this statement
     */
    public /*@non_null@*/ String ident() 
    {
	return delegee.ident();
    }

    /**
     * States that specified class is used.
     */
    public void setUsed() 
    {
	delegee.setUsed();
    }

    /**
     * Indicates whether this simple import statement imports a type.
     *
     * @return	true iff this imports a type
     */
    public boolean isClassImport()
    {
	return delegee.isClassImport();
    }

    /**
     * Indicates whether this simple import statement imports an external
     * generic function.
     *
     * @return	true iff this imports an external generic function
     */
    public boolean isGFImport()
    {
	return delegee.isGFImport();
    }

    /**
     * Registers whether this imports a type or an external generic function.
     */
    public void setImportKind( /*@non_null@*/ FileFinder finder) throws PositionedError {
	delegee.setImportKind(finder);
    }

    /**
     * Indicates whether this is a model import.  */
    public boolean isModel() {
	return isModel;
    }

    /**
     * Make this import statement into a non-model import statement. */
    public void unsetModel() {
	isModel = false;
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Checks whether this class import statement names a class (or
     * generic function) that is used in the source code.  Reports a
     * warning if not.  */
    public void typecheck(/*@non_null@*/ org.multijava.mjc.Main compiler)
    {
	 delegee.typecheck( compiler);
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Accepts the specified visitor
     * @param	p		the visitor
     */
    public void accept(/*@non_null@*/ MjcVisitor p) {
	((JmlVisitor)p).visitJmlClassOrGFImport(this);
    }

    //---------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    //---------------------------------------------------------------------

    private /*@non_null@*/ JClassOrGFImport delegee;
    private boolean isModel;
}
