/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
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
 * $Id: JmlExceptionalExample.java,v 1.5 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;


/**
 * A class representing JML exceptional example specifications. A
 * exceptional example specification is an example specification
 * (<code>example</code>).  The production rule for example
 * specifications is defined as follows.
 *
 * <pre>
 *  example ::= [ [ privacy ] ] "example" ] [ spec-var-decls ]
 *      [ spec-header ] simple-spec-body
 *    | [ privacy ] "exceptional_example" [ spec-var-decls ]
 *      spec-header [ exceptional-example-body ]
 *    | [ privacy ] "exceptional_example" [ spec-var-decls ]
 *      exceptional-example-body
 *    | [ privacy ] "normal_example" [ spec-var-decls ]
 *      spec-header [ normal-example-body ]
 *    | [ privacy ] "normal_example" [ spec-var-decls ]
 *      normal-example-body
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.5 $
 */

public class JmlExceptionalExample extends JmlExample {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Constructs a new instance with given arguments.
     *
     * <pre><jml>
     * requires privacy == 0 ||
     *   privacy == Constants.ACC_PUBLIC ||
     *   privacy == Constants.ACC_PROTECTED ||
     *   privacy == Constants.ACC_PRIVATE;
     * requires specHeader != null;
     * requires specClauses != null;
     * </jml></pre>
     */
    public JmlExceptionalExample(TokenReference where, 
				 long privacy,
                                 JmlSpecVarDecl[] specVarDecls,
                                 JmlRequiresClause[] specHeader,
                                 JmlSpecBodyClause[] specClauses ) {
	super( where, privacy, specVarDecls, specHeader, specClauses );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlExceptionalExample(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

} // JmlExceptionalExample
