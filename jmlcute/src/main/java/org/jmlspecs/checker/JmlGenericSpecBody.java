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
 * $Id: JmlGenericSpecBody.java,v 1.3 2003/08/19 04:29:55 cruby Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;


/**
 * An AST node class for the JML <tt>generic-spec-body</tt>. The production
 * rule <tt>generic-spec-body</tt> is defined as follows.
 *
 * <pre>
 *  generic-spec-body :: = measured_clause ...... ensures_clause
 *    | "{|" generic-spec-case-seq "|}"
 *  generic-spec-case-seq := generic-spec-case [ "also" generic-spec-case ]
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */

public class JmlGenericSpecBody extends JmlSpecBody {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specClauses.length > 0;
    public JmlGenericSpecBody( JmlSpecBodyClause[] specClauses ) {
	super( specClauses );
    }
    
    //@ requires specCases.length > 0;
    public JmlGenericSpecBody( JmlGenericSpecCase[] specCases ) {
	super( specCases );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlSpecBodyClause[] simpleSpecBodies() {
	return specClauses;
    }
    
    public JmlGenericSpecCase[] genericSpecCases() {
	return (JmlGenericSpecCase[])specCases;
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
	    ((JmlVisitor)p).visitJmlGenericSpecBody(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ invariant specCases != null ==>
      @             (\forall int i; 0 <= i && i < specCases.length;
      @                 specCases[i] instanceof JmlGenericSpecCase);
      @*/
}
