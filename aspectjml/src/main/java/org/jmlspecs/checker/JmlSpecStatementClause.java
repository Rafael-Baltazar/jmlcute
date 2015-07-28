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
 * $Id: JmlSpecStatementClause.java,v 1.9 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlSpecStatementClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

/**
 * This abstract class is a common superclass of specification statement clauses
 * (e.g.,  JmlReturnsClause, JmlBreaksClause and JmlContinuesClause).
 */

public abstract class JmlSpecStatementClause extends JmlPredicateClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires predOrNot != null ==> !isNotSpecified;
    //@ requires isNotSpecified ==> predOrNot == null;
    protected JmlSpecStatementClause(/*@ non_null */ TokenReference where,
				      boolean isRedundantly, 
				      /*@ nullable */ JmlPredicate predOrNot,
				      boolean isNotSpecified) {
	super( where, isRedundantly, predOrNot);
	this.isNotSpecified = isNotSpecified;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isNotSpecified() {
	return isNotSpecified;
    }


    /**
     * @return false
     */
    public /*@ pure @*/ boolean isSimpleSpecBody() {
 	return false;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isExceptionalSpecBody() {
	return false;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isNormalSpecBody() {
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

    /** Returns an appropriate context for checking this clause. This
     * method is simply here to make this class a concrete class. */
    protected /*@ non_null @*/ JmlExpressionContext createContext(
	/*@non_null@*/ CFlowControlContextType context) {
        return JmlExpressionContext.createPrecondition( context );
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    //@ invariant predOrNot() != null ==> !isNotSpecified;
    //@ invariant isNotSpecified ==> predOrNot() == null;
    protected boolean isNotSpecified;
}
