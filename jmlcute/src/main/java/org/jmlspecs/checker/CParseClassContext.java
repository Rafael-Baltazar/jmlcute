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
 * $Id: CParseClassContext.java,v 1.8 2005/05/27 13:07:44 chalin Exp $
 */

package org.jmlspecs.checker;

import java.util.Stack;
import java.util.ArrayList;

/**
 * This class is used by the parser to collect the members of a class
 * declaration.  For efficiency (and to avoid memory leaks caused by
 * poor garbage collection in the JVM) a factory method is used to
 * generate instances and old instances are store on a stack for
 * reuse.  It has the same name as its superclass since ANTLR's
 * textual grammar inheritance will then refer to the right
 * (package-local) class.  */
public class CParseClassContext extends org.multijava.mjc.CParseClassContext {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /**
     * Factory method returns an instance of CParseJmlClassContext.  The
     * instance is recycled from the stack of discarded instances or a
     * new instance is minted if the stack is empty.
     * @return	a fresh CParseClassContext instance
     */
    public static org.multijava.mjc.CParseClassContext getInstance() {
	return stack.size() == 0 ?
	    new CParseClassContext() :
	    (CParseClassContext)stack.pop();
    }

    /**
     * Calls the static method <code>release(this)</code>
     */
    public void release() {
	release(this);
    }

    /**
     * Erases the data stored in <code>context</code> and pushes the
     * instance onto a stack for recycling.
     * @param	context	a used instance to be recycled
     */
    public static void release( CParseClassContext context ) {
	context.clear();
	stack.push(context);
    }

    /**
     * Hides the default constructor.
     */ 
    protected CParseClassContext() {}

    /**
     * Prepares this instance for recycling by clearing all the data
     * stored in its ArrayLists.
     */
    protected void clear() {
	super.clear();
	invariants.clear();
	constraints.clear();
	representsDecls.clear();
	axioms.clear();
	varAssertions.clear();
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public void addInvariant( JmlInvariant inv ) {
	invariants.add( inv );
    }

    public /*@non_null*/ JmlInvariant[] invariants() {
	JmlInvariant[] result = new JmlInvariant[ invariants.size() ];
	invariants.toArray( result );
	return result;
    }

    public void addConstraint( JmlConstraint inv ) {
	constraints.add( inv );
    }

    public /*@non_null*/ JmlConstraint[] constraints() {
	JmlConstraint[] result = new JmlConstraint[ constraints.size() ];
	constraints.toArray( result );
	return result;
    }

    public void addRepresentsDecl( JmlRepresentsDecl inv ) {
	representsDecls.add( inv );
    }

    public /*@non_null*/ JmlRepresentsDecl[] representsDecls() {
	JmlRepresentsDecl[] result = new JmlRepresentsDecl[ representsDecls.size() ];
	representsDecls.toArray( result );
	return result;
    }

    public void addAxiom( JmlAxiom inv ) {
	axioms.add( inv );
    }

    public /*@non_null*/ JmlAxiom[] axioms() {
	JmlAxiom[] result = new JmlAxiom[ axioms.size() ];
	axioms.toArray( result );
	return result;
    }

    public void addVarAssertion( JmlVarAssertion varAssert ) {
	varAssertions.add( varAssert );
    }

    public /*@non_null*/ JmlVarAssertion[] varAssertions() {
	JmlVarAssertion[] result 
	    = new JmlVarAssertion[ varAssertions.size() ];
	varAssertions.toArray( result );
	return result;
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * A ArrayList of <code>JmlInvariant</code> instance parsed in the
     * class declaration buffered by this.  */
    private /*@non_null*/ ArrayList invariants = new ArrayList();

    /**
     * A ArrayList of <code>JmlConstraint</code> instance parsed in the
     * class declaration buffered by this.  */
    private /*@non_null*/ ArrayList constraints = new ArrayList();

    /**
     * A ArrayList of <code>JmlRepresentsDecl</code> instance parsed in the
     * class declaration buffered by this.  */
    private /*@non_null*/ ArrayList representsDecls = new ArrayList();

    /**
     * A ArrayList of <code>JmlAxiom</code> instance parsed in the
     * class declaration buffered by this.  */
    private /*@non_null*/ ArrayList axioms = new ArrayList();

    /**
     * A ArrayList of <code>JmlVarAssertion</code> instance parsed in the
     * class declaration buffered by this.  */
    private /*@non_null*/ ArrayList varAssertions = new ArrayList();

    private static /*@non_null*/ Stack stack = new Stack();
}
