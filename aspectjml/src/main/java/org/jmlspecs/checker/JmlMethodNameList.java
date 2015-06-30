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
 * $Id: JmlMethodNameList.java,v 1.1 2005/09/12 19:02:00 cruby Exp $
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
 * @version $Revision: 1.1 $
 */

public class JmlMethodNameList extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires methodNames != null && methodNames.length > 0;
    public JmlMethodNameList( TokenReference where,
			      JmlMethodName methodNames[] ) {
	super( where );
	this.methodNames = methodNames;
	this.storeRefKeyword = null;
    }

    //@ requires storeRefKeyword != null;
    public JmlMethodNameList( TokenReference where,
			      JmlStoreRefKeyword storeRefKeyword ) {
	super( where );
	this.methodNames = null;
	this.storeRefKeyword = storeRefKeyword;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@non_null@*/ CType getType() {
	return CStdType.Boolean;
    }

    public JmlMethodName[] methodNameList() {
	return methodNames;
    }

    public JmlStoreRefKeyword storeRefKeyword() {
	return storeRefKeyword;
    }

    //@ public normal_behavior
    //@   modifies \nothing;
    //@   ensures \result == (storeRefKeyword != null);
    public boolean isStoreRefKeyword() {
	return storeRefKeyword != null;
    }

    //@ public normal_behavior
    //@   modifies \nothing;
    //@   ensures \result != (methodNames != null);
    public boolean isMethodNames() {
	return methodNames != null;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@non_null@*/ String toString()  {
	if (stringRepresentation == null) {
	    if (methodNames != null) {
		StringBuffer result = new StringBuffer( "" );
		for (int i = 0; i < methodNames.length; i++) {
		    if (i>0) {
			result.append( ", " );
		    }
		    result.append( methodNames[i].toString() );
		}
		stringRepresentation = result.toString();
	    } else {
		stringRepresentation = "";
	    }
	}
	return stringRepresentation;
    }

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
	if (methodNames != null)
	    for (int i = 0; i < methodNames.length; i++) {
                // false for no purity check
		methodNames[i].typecheck(context, privacy, false);
            }
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
	    ((JmlVisitor)p).visitJmlMethodNameList(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant methodNames != null || storeRefKeyword != null;
    //@ private invariant !(methodNames != null && storeRefKeyword != null);
    /*@ spec_public @*/ private JmlMethodName methodNames[];
    /*@ spec_public @*/ private JmlStoreRefKeyword storeRefKeyword;
    private String stringRepresentation = null; //@ in objectState;
}
