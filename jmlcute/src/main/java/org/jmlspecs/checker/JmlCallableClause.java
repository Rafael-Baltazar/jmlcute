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
 * $Id: JmlCallableClause.java,v 1.10 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * An AST node class representing the JML <tt>callable</tt> clause.
 * The <tt>callable</tt> is mainly for specifying the subclassing
 * contract. The production rule for the <tt>callable</tt> clause
 * is defined as follows.
 *
 * <pre>
 *  callable-clause ::= callable-keyword callable-methods-list ";"
 *  callable-keyword ::= "callable" | "callable_redundantly"
 *  callable-methods-list ::= method-name-list | store-ref-keyword
 *  store-ref-keyword ::= "\nothing" | "\everything" | "\not_specified"
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.10 $
 */

public class JmlCallableClause extends JmlSpecBodyClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires methodNames != null;
    public JmlCallableClause( /*@ non_null */ TokenReference where,
			      boolean isRedundantly, 
			      /*@ non_null */ JmlMethodNameList methodNames ) {
	super( where, isRedundantly );
	this.methodNames = methodNames;
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //@ pure
    public int preferredOrder() {
	return PORDER_CALLABLE_CLAUSE;
    }

    public /*@ non_null */ JmlMethodNameList methodNames() {
	return methodNames;
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
     * Typechecks this <tt>callable</tt> clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @param privacy the visibility level with which to typecheck
     * @exception PositionedError if any checks fail */
    public void typecheck( /*@non_null@*/ CFlowControlContextType context, 
			   long privacy )
	throws PositionedError
    {
	methodNames.typecheck(context, privacy);
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlCallableClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant methodNames != null;
    /*@ spec_public @*/ private /*@ non_null */ JmlMethodNameList methodNames;
}
