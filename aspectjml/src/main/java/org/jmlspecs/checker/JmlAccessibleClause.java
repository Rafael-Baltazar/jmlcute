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
 * $Id: JmlAccessibleClause.java,v 1.9 2005/07/14 22:23:20 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * An AST node class representing the JML <tt>accessible</tt> clause.
 * The <tt>callable</tt> is mainly for specifying the subclassing
 * contract. The production rule for the <tt>accessible</tt> clause
 * is defined as follows.
 *
 * <pre>
 *  accessible-clause ::= accessible-keyword object-ref-list ";"
 *  object-ref-list ::= object-ref [ "," object-ref ] ...
 *    | store-ref-keyword
 *  object-ref ::= store-ref-expression
 *    | "\other" [ store-ref-name-suffix ] ...
 *  accessible-keyword ::= "accessible" | "accessible_redundantly"
 *  store-ref-keyword ::= "\nothing" | "\everything" | "\not_specified"
 * </pre>
 *
 * For the definition of <tt>store-ref-expression</tt> and
 * <tt>store-ref-name-suffix</tt>, refer to the class <tt>JmlStoreRef</tt>.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public class JmlAccessibleClause extends JmlSpecBodyClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires storeRefs != null && storeRefs.length > 0;
    public JmlAccessibleClause( TokenReference where,
				boolean isRedundantly, 
				JmlStoreRef storeRefs[] ) {
	super( where, isRedundantly );
	this.storeRefs = storeRefs;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //@ pure
    public int preferredOrder() {
	return PORDER_CALLABLE_CLAUSE;
    }

    public JmlStoreRef[] storeRefs() {
	return storeRefs;
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

    /**
     * Typechecks this <code>accessible</code> clause in the given
     * visibility, <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context, long privacy ) 
	throws PositionedError
    {
	for (int i = 0; i < storeRefs.length; i++) {
	    // create a new precondition expression context 
	    JmlExpressionContext ectx = 
		JmlExpressionContext.createPrecondition( context );

	    //@ assert storeRefs[i] != null;
	    storeRefs[i] = storeRefs[i].typecheck(ectx, privacy);
	}
        
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
	    ((JmlVisitor)p).visitJmlAccessibleClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant storeRefs != null && storeRefs.length > 0;
    private JmlStoreRef storeRefs[];
}
