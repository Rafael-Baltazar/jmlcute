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
 * $Id: JmlExceptionalSpecCase.java,v 1.2 2002/03/15 21:43:16 cclifton Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;

/**
 * An AST node class for the JML <tt>exceptional-spec-case</tt>. The production
 * rule <tt>exceptional-spec-case</tt> is defined as follows.
 *
 * <pre>
 *  exceptional-spec-case :: = [ spec-var-decls ] spec-header [ exceptional-spec-body ]
 *    | [ spec-var-decls ] exceptional-spec-body
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.2 $
 */

public class JmlExceptionalSpecCase extends JmlGeneralSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specHeader != null ==> specHeader.length > 0;
    //@ requires specVarDecls != null ==> specVarDecls.length > 0;
    //@ requires specHeader != null || exceptionalSpecBody != null;
    public JmlExceptionalSpecCase(TokenReference sourceRef,
			      JmlSpecVarDecl[] specVarDecls,
			      JmlRequiresClause[] specHeader,
			      JmlExceptionalSpecBody exceptionalSpecBody) {
	super(sourceRef, specVarDecls, specHeader, exceptionalSpecBody);
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlExceptionalSpecBody exceptionalSpecBody() {
	return (JmlExceptionalSpecBody) specBody;
    }

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
	    ((JmlVisitor)p).visitJmlExceptionalSpecCase(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
}
