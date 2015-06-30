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
 * $Id: JmlReachExpression.java,v 1.9 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * An AST node class for the JML reach expressions. The JML reach expression
 * is used to denote all the objects that is reachable from a particular
 * object or a set of objects. The syntax for the reach expression is
 * defined as follows.
 *
 * <pre>
 *  jml-primary ::= ...
 *    | "\reach" "(" spec-expression [ "," reference-type [ ","
 *      store-ref-expression ] ] ")"
 *    | ...
 * </pre>
 *
 * Refer to the class <tt>JmlStoreRefExpression</tt> for the definition
 * of the production rule <tt>store-ref-expression</tt>.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public class JmlReachExpression extends JmlSpecExpressionWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlReachExpression( /*@non_null@*/TokenReference where, 
			       /*@non_null@*/ JmlSpecExpression specExpression,
			       /*@non_null@*/ CType referenceType, 
			       /*@nullable@*/JmlStoreRefExpression storeRefExpression ) {
	super( where, specExpression );
	this.referenceType = referenceType;
	this.storeRefExpression = storeRefExpression;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@non_null@*/ CType referenceType() {
	return referenceType;
    }

    public /*@nullable@*/ JmlStoreRefExpression storeRefExpression() {
	return storeRefExpression;
    }

    public /*@non_null@*/ CType getType() {
	return JmlStdType.JMLObjectSet;
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
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return a desugared Java expression
     * @exception PositionedError if the check fails */
    public /*@non_null@*/ JExpression typecheck( /*@non_null@*/ CExpressionContextType context ) 
	throws PositionedError 
    {
	// The type checking rules for the \reach expression
	// are as follows.
	// 
	// 1. Of the form: \reach(x)
	//    - x must be of a reference type (including arrays)
	// 2. Of the form: \reach(x, T)
	//    - x must be of a reference type
	//    - T muse be a  reference type
	// 3. Of the form: \reach(x, T, f)
	//    - x must be of a reference type
	//    - T muse be a (non-array?) reference type
	//    - f is a valid field reference of type T.

	//@ assert specExpression != null;
	specExpression = 
	    (JmlSpecExpression) specExpression.typecheck( context );
	
	check( context, 
	       specExpression.getType().isReference(),
	       JmlMessages.NOT_REFERENCE_EXPRESSION_IN_REACH, 
	       specExpression.getType() );

	// is of the form: \reach(x, T) or \reach(x, T, f)?
	if (referenceType != null) {
	    try {
		referenceType = referenceType.checkType( context );
	    }
	    catch (UnpositionedError e) {
		throw new PositionedError(getTokenReference(),
					  JmlMessages.TYPE_UNKNOWN,
					  referenceType );
	    }
	    
	    // is of the form: \reach(x, T)
	    if (storeRefExpression == null) {
		// T must be reference type
		check( context, 
		       referenceType.isReference(),
		       JmlMessages.NOT_REFERENCE_TYPE_IN_REACH,
		       referenceType );
	    } else {
		// It is of the form: \reach(x, T, f).
		// T must be non-arrray reference type
		check( context, 
		       referenceType.isReference() && 
		         !referenceType.isArrayType(),
		       JmlMessages.NOT_NON_ARRAY_REFERENCE_TYPE_IN_REACH, 
		       referenceType );
	    }

	    // is of the form \fields_of(x, T, f) with class type T?
	    if (storeRefExpression != null
		&& referenceType.isReference() 
		&& !referenceType.isArrayType()) {
		storeRefExpression = (JmlStoreRefExpression) 
		    storeRefExpression.typecheck( context, 
                                                  ACC_PRIVATE,
                                                  referenceType );
	    }
	}
	return this;
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
	    ((JmlVisitor)p).visitJmlReachExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@non_null@*/ CType referenceType;

    //@ private invariant storeRefExpression != null ==> referenceType != null;
    private /*@ nullable */ JmlStoreRefExpression storeRefExpression;

}
