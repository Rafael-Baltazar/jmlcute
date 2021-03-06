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
 * $Id: JmlReturnsClause.java,v 1.4 2003/06/26 10:17:41 davidcok Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlReturnsClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.4 $
 */

public class JmlReturnsClause extends JmlSpecStatementClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires predOrNot != null ==> !isNotSpecified;
    //@ requires isNotSpecified ==> predOrNot == null;
    public JmlReturnsClause( TokenReference where,
			     boolean isRedundantly, 
			     JmlPredicate predOrNot,
			     boolean isNotSpecified) {
	super( where, isRedundantly, predOrNot, isNotSpecified);
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //@ pure
    public int preferredOrder() {
	return PORDER_RETURNS_CLAUSE;
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

    /** Returns an appropriate context for checking this clause. This
     * method is simply here to make this class a concrete class. */
    protected JmlExpressionContext createContext(
        CFlowControlContextType context) {
        return JmlExpressionContext.createPostcondition( context );
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlReturnsClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
}
