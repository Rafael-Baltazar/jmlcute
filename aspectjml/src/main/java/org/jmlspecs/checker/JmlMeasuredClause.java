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
 * $Id: JmlMeasuredClause.java,v 1.9 2005/09/12 19:02:00 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlMeasuredClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public class JmlMeasuredClause extends JmlPredicateClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlMeasuredClause( TokenReference where,
			      boolean isRedundantly, 
			      JmlSpecExpression specExp,
			      JmlPredicate pred ) {
	super( where, isRedundantly, pred );
	this.specExp = specExp;

        // make an int-typed informal description if necessary
        if (specExp != null &&
            (specExp.expression() instanceof JmlInformalExpression)) {
            this.specExp = new JmlSpecExpression(
                JmlInformalExpression.ofInteger(
                    (JmlInformalExpression) specExp.expression()));
        }
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ int preferredOrder() {
	return PORDER_MEASURED_CLAUSE;
    }

    public /*@ pure @*/ JmlSpecExpression specExp() {
	return specExp;
    }

    public /*@ pure @*/ boolean isNotSpecified() {
	return specExp == null;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isSimpleSpecStatementBody() {
	return false;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isAbruptSpecBody() {
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

    /**
     * Typechecks this <code>measured_by</code> clause in the context in which
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

	//@ assert specExp != null;

	// create a new precondition expression context 
	JmlExpressionContext ectx = createContext( context );

	specExp = (JmlSpecExpression) specExp.typecheck( ectx, privacy );
	check(context, specExp.getType().isOrdinal(),
	      JmlMessages.BAD_TYPE_IN_MEASURED_CLAUSE,
	      specExp.getType().toVerboseString() ); // WMD
	
	if (predOrNot != null) {
	    predOrNot = (JmlPredicate) predOrNot.typecheck( ectx, privacy );
        }
    }

    /** Returns an appropriate context for checking this clause. */
    protected JmlExpressionContext createContext(
        CFlowControlContextType context) {
        return JmlExpressionContext.createPrecondition( context );
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
	    ((JmlVisitor)p).visitJmlMeasuredClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    //@ private invariant specExp == null ==> predOrNot == null;
    private JmlSpecExpression specExp;
}
