/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
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
 * $Id: JFieldDeclarationWrapper.java,v 1.9 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CSourceField;
import org.multijava.mjc.JFieldDeclaration;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.TokenReference;

/**
 * A class representing a field declaration in the syntax tree. This class
 * provides JML-specific handling of field declaration by overriding several
 * inherited methods. For example, the <code>checkInterface</code> method
 * now creates and returns an object of {@link JmlSourceClass} in place of
 * {@link CSourceClass}, that will be registered in the signature forest and
 * can handle JML-specific behaviors (e.g., spec_public-ness).
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */
public class JFieldDeclarationWrapper extends JFieldDeclaration 
    implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a node in the parsing tree.
     * This method is directly called by the parser.
     * @param	where		the line of this node in the source code
     * @param	variable	the variable definition
     * @param	javadoc		is this field deprecated
     * @param	comments	non-javadoc comments for this field
     */
    public JFieldDeclarationWrapper(/*@non_null@*/ TokenReference where,
				    /*@non_null@*/ JVariableDefinition variable,
				    /*@nullable@*/ JavadocComment javadoc,
				    /*@nullable@*/ JavaStyleComment[] comments) {
	super(where, variable, javadoc, comments);
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /*
     * Checks the basic interfaces to make sure things generally look OK. 
     * This pass gathers information about the type signatures of everything 
     * (imported class files, classes being compiled, methods, fields, etc...)
     * needed for the later passes.  This information is stored 
     * in a context hierarchy that is bound to the AST.
     *
     * @param context the context in which this field appears
     * @return the signature of this field
     * @exception PositionedError an error with reference to the source file
    public CSourceField checkInterface(CClassContextType context) 
	throws PositionedError 
    {
	return super.checkInterface(context);
    }
     */

    /**
     * Generates the signature object for this field declaration. 
     * This method overrides the inherited method to generate JML-specific
     * signature object, i.e., an instance of {@link JmlSourceField}.
     *
     * @param owner	the class signature singleton for the logical outer 
     *			class of this, or null if this is a top level 
     *			declaration
     */
    protected /*@non_null@*/ CSourceField makeFieldSignature( /*@non_null@*/ CClass owner )
    {
	JVariableDefinition variable = variable();
	long modifiers = modifiers();

	JmlMemberAccess access = new JmlMemberAccess( owner, modifiers );

	JmlSourceField self = new JmlSourceField( access,
						  variable.ident(),
						  variable.getType(),
						  isDeprecated() );
	return self;
    }
}
