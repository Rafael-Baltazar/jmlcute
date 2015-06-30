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
 * $Id: JmlNormalSpecBody.java,v 1.6 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.MjcVisitor;

/**
 * An AST node class for the JML <tt>normal-spec-body</tt>. The production
 * rule <tt>normal-spec-body</tt> is defined as follows.
 *
 * <pre>
 *  normal-spec-body :: = measured_clause ...... ensures_clause
 *    | "{|" normal-spec-case-seq "|}"
 *  normal-spec-case-seq := normal-spec-case [ "also" normal-spec-case ]
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.6 $
 */

public class JmlNormalSpecBody extends JmlSpecBody {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specClauses != null && specClauses.length > 0;
    public JmlNormalSpecBody( /*@ non_null */ JmlSpecBodyClause[] specClauses ) {
	super( specClauses );
    }
    
    //@ requires specCases != null && specCases.length > 0;
    /*@ requires (\forall int i; 0 <= i && i < specCases.length;
      @              specCases[i] instanceof JmlNormalSpecCase);
      @*/
    public JmlNormalSpecBody(/*@non_null*/ JmlGeneralSpecCase[] specCases ) {
	super( specCases );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@non_null@*/ JmlNormalSpecCase[] normalSpecCases() {
	return (JmlNormalSpecCase[])specCases;
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
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlNormalSpecBody(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ invariant specCases != null ==>
      @   (\forall int i; 0 <= i && i < specCases.length;
      @       specCases[i] instanceof JmlNormalSpecCase);
      @*/
}
