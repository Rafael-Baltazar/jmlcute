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
 * $Id: JmlConstraint.java,v 1.14 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;

/**
 *
 * This AST node represents a JML constraint annotation.
 * The syntax for the history constraint is as follows.
 *
 * <pre>
 *  constraint ::= constraint-keyword predicate "for" constrained-list ";"
 *  constraint-keyword ::= "constraint" | "constraint_redundantly"
 *  constrained-list ::= method-name-list | "\everything"
 *  method-name-list ::= method-name [ "," method-name ] ...
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.14 $
 */
public class JmlConstraint extends JmlDeclaration {

    /**
     * Creates a new <code>JmlConstraint</code> instance.
     *
     * @param where a <code>TokenReference</code> value
     * @param modifiers modifier bit-mask
     * @param redundantly true ==> this is a constraint_redundantly statement
     * @param predicate a <code>JmlPredicate</code> value
     * @param methodNames the methods for which this constraint applies,
     *			  this applies to all methods if (methodNames==null)
     */
    public JmlConstraint( /*@non_null@*/ TokenReference where, long modifiers, 
			  boolean redundantly, 
			  /*@non_null@*/ JmlPredicate predicate, 
			  /*@nullable@*/ JmlMethodNameList methodNames ) 
    {
	super( where, modifiers, redundantly );
	this.predicate = predicate;
	this.methodNames = methodNames;
    }

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    /**
     * Indicates whether this constraint applies for all methods (as
     * indicated by a <code>for &bs;everything</code> constrained-list
     * or by the absence of any constrained-list.
     *
     * <pre><jml>
     * ensures \result <==> methodNames == null;
     * </jml></pre>
     * 
     */
    public /*@ pure @*/ boolean isForEverything() {
	return methodNames == null;
    }

    /**
     * Gives the list of method-names to which this constraint
     * applies.  */
    public /*@non_null@*/ JmlMethodNameList methodNames() {
	if (methodNames == null) {
	    return  new JmlMethodNameList( getTokenReference(),
					   new JmlMethodName[0] );
	}
	return methodNames;
    }
	
    public /*@non_null@*/ JmlPredicate predicate() {
		return predicate;
	}

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@non_null@*/ String toString()  {
	StringBuffer result = new StringBuffer( "constraint" );
	if (redundantly) {
	    result.append( "_redundantly" );
	} // end of if 
	result.append( " " ).append( predicate.toString() );
	if (methodNames != null) {
	    result.append( " for " );
	    result.append( methodNames.toString() );
	}
	result.append( ";" );
	return result.toString();
    }


    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this invariant clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public void typecheck( /*@non_null@*/ CContextType context ) 
	throws PositionedError 
    {
	try {
	    enterSpecScope();

            checkModifiers(context);
	    JmlExpressionContext ectx = createContext( context );
	    predicate = (JmlPredicate) predicate.typecheck( ectx, privacy() );

	    if (!isForEverything()) {
		methodNames.typecheck( ectx.getFlowControlContext(),
				       privacy());
	    }
	}
	finally {
	    exitSpecScope();
	}
    }

    /**
     * Create a JmlExpressionContext object as a child of the given
     * (CClassContextType) context that can be used to typecheck
     * this JML declaration.
     *
     * @param context the pararent context
     */
    protected /*@non_null@*/ JmlExpressionContext createContext( /*@non_null@*/ CContextType context ) 
    {
        CFlowControlContextType fctx = createContextHelper(context);
        return JmlExpressionContext.createIntercondition(fctx);
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
	    ((JmlVisitor)p).visitJmlConstraint( this );
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    /**
     * An AST for the predicate clause of this constraint.  */
    protected /*@non_null@*/ JmlPredicate predicate;

    /**
     * The methods to which this constraint applies.  This constraint
     * applies to all methods if <code>methodNames == null</code>.  */
    /*@ spec_public @*/ protected /*@ nullable */ JmlMethodNameList methodNames;
    
}// JmlConstraint
