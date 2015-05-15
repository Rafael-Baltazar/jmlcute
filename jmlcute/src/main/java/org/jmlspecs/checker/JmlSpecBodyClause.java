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
 * $Id: JmlSpecBodyClause.java,v 1.10 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * This abstract class is the common superclass of different kinds of
 * specification clauses appearing in the specification body such as
 * JmlAccessibleClause, JmlAssignableClause, JmlCallableClause, and
 * JmlPredicateClause.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.10 $
 */

public abstract class JmlSpecBodyClause extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    protected JmlSpecBodyClause( /*@ non_null */ TokenReference where, 
			      boolean isRedundantly ) {
	super( where );
	this.isRedundantly = isRedundantly;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isRedundantly() {
	return isRedundantly;
    }

    // expected to be redefined by subclass;
    public /*@ pure @*/ int preferredOrder() {
	return PORDER_UNKNOWN;
    }

    /**
     * @return true
     */
    public /*@ pure @*/ boolean isSimpleSpecBody() {
	return true;
    }

    /**
     * @return true
     */
    public /*@ pure @*/ boolean isExceptionalSpecBody() {
	return true;
    }

    /**
     * @return true
     */
    public /*@ pure @*/ boolean isNormalSpecBody() {
	return true;
    }

    /**
     * @return true
     */
    public /*@ pure @*/ boolean isSimpleSpecStatementBody() {
	return true;
    }

    /**
     * @return true
     */
    public /*@ pure @*/ boolean isAbruptSpecBody() {
	return true;
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
     * Typechecks this specification body clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    abstract public void typecheck( /*@non_null@*/ CFlowControlContextType context, 
                                   long privacy)
	throws PositionedError;

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    protected boolean isRedundantly;

    public    final static int PORDER_UNKNOWN           = -1;
    protected final static int PORDER_DIVERGES_CLAUSE   = 1;
    protected final static int PORDER_MEASURED_CLAUSE   = 1;
    protected final static int PORDER_ASSIGNABLE_CLAUSE = 2;
    protected final static int PORDER_ACCESSABLE_CLAUSE = 2;
    protected final static int PORDER_CALLABLE_CLAUSE   = 2;
    protected final static int PORDER_CAPTURES_CLAUSE   = 2;
    protected final static int PORDER_WHEN_CLAUSE       = 3;
    protected final static int PORDER_WORKING_SPACE_CLAUSE = 4;
    protected final static int PORDER_DURATION_CLAUSE   = 4;
    protected final static int PORDER_ENSURES_CLAUSE    = 5;
    protected final static int PORDER_SIGNALS_CLAUSE    = 6;
    protected final static int PORDER_CONTINUES_CLAUSE  = 7;
    protected final static int PORDER_BREAKS_CLAUSE     = 7;
    protected final static int PORDER_RETURNS_CLAUSE    = 7;
}
