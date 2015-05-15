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
 * $Id: JmlExceptionalSpecBody.java,v 1.4 2003/08/19 04:29:55 cruby Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;

/**
 * An AST node class for the JML <tt>exceptional-spec-body</tt>. 
 * The production rule <tt>exceptional-spec-body</tt> is defined as follows.
 *
 * <pre>
 *  exceptional-spec-body :: = measured_clause ...... signals_clause
 *    | "{|" exceptional-spec-case-seq "|}"
 *  exceptional-spec-case-seq := exceptional-spec-case [ "also" exceptional-spec-case ]
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.4 $
 */

public class JmlExceptionalSpecBody extends JmlSpecBody {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specClauses != null && specClauses.length > 0;
    public JmlExceptionalSpecBody( JmlSpecBodyClause[] specClauses ) {
	super( specClauses );
    }
    
    /*@ requires specCases != null && specCases.length > 0;
      @ requires (\forall int i; 0 <= i && i < specCases.length;
      @              specCases[i] instanceof JmlExceptionalSpecCase);
     */
    public JmlExceptionalSpecBody( JmlGeneralSpecCase[] specCases ) {
	super( specCases );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlExceptionalSpecCase[] normalSpecCases() {
	return (JmlExceptionalSpecCase[])specCases;
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
	    ((JmlVisitor)p).visitJmlExceptionalSpecBody(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ invariant specCases != null ==>
      @   (\forall int i; 0 <= i && i < specCases.length;
      @       specCases[i] instanceof JmlExceptionalSpecCase);
     */
}
