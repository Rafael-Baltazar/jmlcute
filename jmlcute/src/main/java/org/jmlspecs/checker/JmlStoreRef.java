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
 * $Id: JmlStoreRef.java,v 1.17 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.mjc.MjcVisitor;

/**
 * An abstraction of JML store references. This abstract class represents
 * AST nodes for JML store references, and is the superclass of all their
 * variations. The JML store reference (<tt>store-ref</tt>) is defined
 * as follows.
 *
 * <pre>
 *  store-ref ::= store-ref-expression
 *    | "\fields_of" "(" spec-expression [ "," reference-type 
 *      [ "," store-ref-expression ] ] ")"
 *    | informal-description
 *    | store-ref-keyword
 *  store-ref-expression ::= store-ref-name [ store-ref-name-suffix ] ...
 *  store-ref-name ::= ident | "super" | "this"
 *  store-ref-name-suffix ::= "." ident | "[" spec-array-ref-expr "]"
 *  spec-array-ref-expr ::= spec-expression
 *    | spec-expression ".." spec-expression
 *    | "*"
 *  store-ref-keyword ::= "\nothing" | "\everything" | "not_specified"
 * </pre>
 *
 * The subclasses <tt>JmlInformalStoreRef</tt>,
 * <tt>JmlStoreRefExpression</tt>, <tt>JmlOtherRef</tt>, 
 * and <tt>JmlStoreRefKeyword</tt> 
 * implement ASTS for the productions rules <tt>"\fields_of"</tt> branch
 * of <tt>store-ref</tt>, <tt>informal-description</tt>, 
 * <tt>store-ref-expression</tt>, <tt>object-ref</tt>, 
 * and <tt>store-ref-keyword</tt> 
 * respectively.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.17 $
 */

public abstract class JmlStoreRef extends JmlNode implements Cloneable {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlStoreRef( /*@ non_null */ TokenReference where ) {
	super( where );
    }

    //---------------------------------------------------------------------
    // Visitor
    //---------------------------------------------------------------------

    public void accept(/*@non_null@*/ MjcVisitor m) {
		((JmlVisitor)m).visitJmlStoreRef(this);
	}
    
    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@non_null@*/ Object clone() {
	try {
	    return super.clone();
	} catch( CloneNotSupportedException e ) {
	    // Superclass should be clonable. It declares
	    // CloneNotSupportedException so that subclasses can
	    // choose to not be clonable.

	    //@ unreachable; 
	    return null;
	}
    }
    
    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isNothing() {
	return false;
    }

    public /*@ pure @*/ boolean isNothingOrNotSpecified() {
	return isNothing() || isNotSpecified();
    }

    public /*@ pure @*/ boolean isEverything() {
	return false;
    }

    public /*@ pure @*/ boolean isNotSpecified() {
	return false;
    }

    public boolean isPrivateData() {
	return false;
    }

    public boolean isStoreRefExpression() {
	return false;
    }

    public boolean isInformalStoreRef() {
	return false;
    }

    /** Returns true iff the store ref expression accesses a field
     *  of a model field.
     *  This method must be called after type checking. */
    public boolean isInvalidModelFieldRef() {
	return false;
    }

    //@ ensures (* returns true iff this does not reference non-local variables *);
    public /*@ pure @*/ boolean isLocalVarReference() {
	return false; // default is conservative
    }

    /** Returns true iff the store ref expression is the pseudo 
     *  variable 'super'. 
     *  This method must be called after type checking. */
    public boolean isSuperExpression() {
	return false; // default is conservative
    }

    /** Returns true iff the ref expression is the receiver 'this'. 
     *  This method must be called after type checking. */
    public boolean isThisExpression() {
	return false; // default is conservative
    }

    /** Returns true if the store-ref expression refers to a field 
     *  of the current receiver (this).
     */
    public boolean isFieldOfReceiver() {
	return false; // default is conservative
    }

    /**
     * Typechecks this store reference in the given visibility,
     * <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @return a desugared store reference
     * @exception PositionedError if the check fails 
     */
    abstract public /*@ non_null */ JmlStoreRef typecheck(/*@non_null@*/ CExpressionContextType context,
                                          long privacy)
	throws PositionedError;

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlStoreRef
