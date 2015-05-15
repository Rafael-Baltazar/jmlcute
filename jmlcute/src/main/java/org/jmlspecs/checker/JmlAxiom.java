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
 * $Id: JmlAxiom.java,v 1.9 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 *
 * This AST node represents a JML axiom annotation. The syntax for the
 * axiom annotation is defined as follows.
 *
 * <pre>
 *  field ::= ......
 *    | "axiom" predicate ";"
 *    | ......
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.9 $
 */

public class JmlAxiom extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlAxiom( /*@ non_null */ TokenReference where, /*@non_null@*/ JmlPredicate predicate ) {
	super( where );
	this.predicate = predicate;
    }

    public /*@non_null@*/ Object clone() {
	try {
	    return super.clone();
	} catch ( CloneNotSupportedException e ) {
	    // Superclass should be clonable. It declares
	    // CloneNotSupportedException so that subclasses can
	    // choose to not be clonable.
	    throw new IllegalStateException("unreachable code reached!");
	}
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public /*@non_null@*/ JmlPredicate predicate() {
	return predicate;
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
     * Typechecks this invariant clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public void typecheck( /*@non_null@*/ CContextType context ) throws PositionedError 
    {
	try {
	    enterSpecScope();

	    JmlExpressionContext ectx = createContext( context );
	    predicate = (JmlPredicate) predicate.typecheck( ectx );
	}
	finally {
	    exitSpecScope();
	}
    }

    /**
     * Create a <code>JmlExpressionContext</code> object as a child of 
     * the given (CClassContextType) context, which is suitable for 
     * checking this axiom clause.
     *
     * @param context the pararent context
     */
    protected /*@non_null@*/ JmlExpressionContext createContext( /*@non_null@*/ CContextType context ) 
    {
        // We check axiom clauses in a static context. ESC/Java says
        // "Axioms may not mention this or \lockset." [ESC/Java 2.4.2].

        // dummy declaration to host typechecking of JML axiom.
        JMethodDeclaration init = // true for static
            new DummyInitializerDeclaration(getTokenReference(), true);

        // generate signaure (CMethod) object
        try {
            init.checkInterface( context ); 
        } catch (PositionedError e1) {
	    throw new RuntimeException("Unreachable! " +  e1.getMessage());
	}

        CMethodContextType mctx = 
            init.createSelfContext((CClassContextType)context);
        CFlowControlContextType fctx = 
	    mctx.createFlowControlContext( 0, getTokenReference() );

        // !FIXME! a new kind of context is needed to disallow "\lockset".
        return JmlExpressionContext.createIntracondition( fctx );
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
	    ((JmlVisitor)p).visitJmlAxiom(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@non_null@*/ JmlPredicate predicate;
    
}// JmlAxiom
