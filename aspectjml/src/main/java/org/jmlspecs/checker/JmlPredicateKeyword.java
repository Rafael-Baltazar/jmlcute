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
 * $Id: JmlPredicateKeyword.java,v 1.1 2005/09/07 19:42:14 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;

public class JmlPredicateKeyword extends JmlPredicate
{


    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /*@ requires code == Constants.NOT_SPECIFIED || code == Constants.SAME;
      @*/
    public JmlPredicateKeyword( TokenReference where, int code ) {
	super( new JmlSpecExpression(new JBooleanLiteral(where, false)) );
	// !FIXME! this is a temporary precondition to be changed 
	//         to the proper precondition by the RAC.
	this.code = code;
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isSameKeyword() {
	return code == Constants.SAME;
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
    public void accept( /*@non_null@*/  MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlPredicateKeyword( this );
	else
	    throw new UnsupportedOperationException( JmlNode.MJCVISIT_MESSAGE );
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private final int code;

    // -------------------------------------------------------------
    // STATIC UTILITIES
    // -------------------------------------------------------------
}
