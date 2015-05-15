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
 * $Id: JmlPackageImport.java,v 1.7 2003/09/02 19:27:21 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.JPackageImport;
import org.multijava.mjc.JPackageImportType;
import org.multijava.mjc.JPackageName;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.TokenReference;

/**
 * This type represents (in the AST) full-package import statements. 
 * For example, <code>import java.util.*;</code>. 
 */
public class JmlPackageImport extends JmlNode implements JPackageImportType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * @param	where		the token reference of this node
     * @param	name		the package name
     * @param	comments	non-javadoc style comments for this statement
     * @param isModel		indicates whether this is a model import
     */
    public JmlPackageImport( TokenReference where, 
			   String name, 
			   JavaStyleComment[] comments,
			   boolean isModel ) {
	super(where);		// cached
	this.delegee = new JPackageImport( where, name, comments );
	this.isModel = isModel;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS & MUTATORS
    // ----------------------------------------------------------------------

    /**
     * Returns the package name defined by this declaration.
     *
     * @return	the package name defined by this declaration
     */
    public String getName()
    {
	return delegee.getName();
    }

    /**
     * States that specified class in imported package is used.
     * @param	clazz		the class that is used.
     */
    public void setClassUsed(String clazz)
    {
	 delegee.setClassUsed( clazz);
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
     * Checks the use of package import statements.  Issues warnings
     * for things like unused packages being imported or a package
     * import being used when only a small number of classes from the
     * package are actually referenced.  In general these are
     * stylistic issues.  
     * @param	compiler	the compiler calling this method
     * @param	pack		the name of the package being imported */
    public void typecheck( org.multijava.mjc.Main compiler, JPackageName pack )
    {
	 delegee.typecheck(  compiler,  pack );
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Accepts the specified visitor
     * @param	p		the visitor
     */
    public void accept(MjcVisitor p) {
	((JmlVisitor)p).visitJmlPackageImport(this);
    }

    //---------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    //---------------------------------------------------------------------

    private JPackageImport delegee;
    private boolean isModel;
}
