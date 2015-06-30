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
 * $Id: JmlEnsuresClause.java,v 1.9 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;

/**
 * A JML AST node for the <\code>ensures</code> clause.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public class JmlEnsuresClause extends JmlPredicateClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlEnsuresClause(/*@ non_null */ TokenReference where,
			      boolean isRedundantly, /*@ nullable */ JmlPredicate predOrNot ) {
	super( where, isRedundantly, predOrNot );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //@ pure
    public int preferredOrder() {
	return PORDER_ENSURES_CLAUSE;
    }

    /**
     * @return false
     */
    //@ pure
    public boolean isExceptionalSpecBody() {
	return false;
    }

    /**
     * @return false
     */
    //@ pure
    public boolean isAbruptSpecBody() {
	return false;
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

    /** Returns an appropriate context for checking this clause. */
    protected /*@non_null@*/ JmlExpressionContext createContext(
        /*@non_null@*/ CFlowControlContextType context) {
        return JmlExpressionContext.createPostcondition( context );
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept(/*@non_null@*/  MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlEnsuresClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
}
