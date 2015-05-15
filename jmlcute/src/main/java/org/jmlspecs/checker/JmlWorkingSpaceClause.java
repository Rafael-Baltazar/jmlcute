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
 * $Id: JmlWorkingSpaceClause.java,v 1.5 2005/09/12 19:02:00 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlWorkingSpaceClause.java
 *
 * @author Gary T. Leavens
 * @version $Revision: 1.5 $
 */

public class JmlWorkingSpaceClause extends JmlPredicateClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlWorkingSpaceClause( TokenReference where,
			      boolean isRedundantly, 
			      JmlSpecExpression specExp,
			      JmlPredicate pred ) {
	super( where, isRedundantly, pred );
	this.specExp = specExp;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ int preferredOrder() {
	return PORDER_WORKING_SPACE_CLAUSE;
    }

    public /*@ pure @*/ JmlSpecExpression specExp() {
	return specExp;
    }

    public /*@ pure @*/ boolean isNotSpecified() {
	return specExp == null;
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
     * Typechecks this <code>working_space</code> clause in the context in which
     * it appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context, long privacy )
	throws PositionedError
    {
	if (isNotSpecified())
	    return;

	// create a new working space expression context 
	JmlExpressionContext ectx = createContext( context );
	
	//@ assert specExp != null;
	specExp = (JmlSpecExpression) specExp.typecheck( ectx, privacy );
	check(context, specExp.getType().isOrdinal(),
	      JmlMessages.BAD_TYPE_IN_WORKING_SPACE_CLAUSE,
              specExp.getType().toVerboseString() ); // WMD
	
	if (predOrNot != null) {
	    predOrNot = (JmlPredicate) predOrNot.typecheck(
                // !FIXME! this allows \result in exceptional behaviors...
                JmlExpressionContext.createPostcondition( context ),
                privacy );
        }
    }

    /** Returns an appropriate context for checking this clause. */
    protected JmlExpressionContext createContext(
        CFlowControlContextType context) {
        return JmlExpressionContext.createWorkingSpace( context );
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
	    ((JmlVisitor)p).visitJmlWorkingSpaceClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    //@ private invariant specExp == null ==> predOrNot == null;
    private JmlSpecExpression specExp;
}
