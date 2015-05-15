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
 * $Id: JmlPredicateClause.java,v 1.3 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlPredicateClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */

/**
 * This abstract class represents a specfication body clause that
 * allows the predicate or expression to be replaced by
 * <code>\not_specified</code> (e.g., JmlDivergesClause,
 * JmlEnsuresClause, JmlWorkingSpaceClause, JmlDurationClause,
 * JmlMeasuredClause, JmlRequiresClause, JmlSignalsClause,
 * JmlSpecStatementClause, and JmlWhenClause).
 */
public abstract class JmlPredicateClause extends JmlSpecBodyClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    protected JmlPredicateClause( /*@ non_null */ TokenReference where, boolean isRedundantly, 
    		/*@ nullable */ JmlPredicate predOrNot ) 
    {
	super( where, isRedundantly );
	this.predOrNot = predOrNot;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean hasSamePredicate() {
	return (predOrNot == null)? false : predOrNot.isSameKeyword();
    }

    public /*@ pure @*/ JmlPredicate predOrNot() {
	return predOrNot;
    }

    /**
     * Indicates whether this clause has the predicate
     * <code>not_specified</code>.  
     *
     * <pre><jml>
     * ensures \result == (predOrNot == null);
     * </jml></pre>
     *
     */
    public /*@ pure @*/ boolean isNotSpecified() {
	return predOrNot == null;
    }

    public abstract void accept(/*@non_null@*/ MjcVisitor m);
	
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
     * Typechecks this clause with the privacy, <code>privacy</code>,
     * in the context in which it appears. Mutates the context to
     * record the information learned during checking.
     *
     * <pre><jml>
     * also
     *   requires privacy == ACC_PUBLIC || privacy == ACC_PROTECTED ||
     *     privacy == ACC_PRIVATE || privacy == 0;
     * </jml></pre>
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck(/*@ non_null @*/  CFlowControlContextType context, 
			  long privacy )
	throws PositionedError
    {
	if (isNotSpecified())
	    return;

        // check predicate
        JmlExpressionContext ectx = createContext(context);

	// This try block allows us to display errors from more than 
	// one clause 
	try {
	    predOrNot = (JmlPredicate) predOrNot.typecheck( ectx, privacy );
	} catch (PositionedError e) {
	    context.reportTrouble(e);
	}
    }

    /** Returns an appropriate context for checking this clause. */
    abstract protected JmlExpressionContext createContext(
        /*@non_null*/ CFlowControlContextType context);

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ invariant predOrNot == null ==> 
      @               (* the predicate is a \not_specified *);
      @*/
    /*@ spec_public @*/ protected /*@ nullable */ JmlPredicate predOrNot;
}
