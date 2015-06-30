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
 * $Id: JmlName.java,v 1.12 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents a store-ref-name, store-ref-name-suffix,
 * method-res-start, or identifier from a method-ref in an AST.
 * Several overloaded constructors are used to generate the various
 * sorts of expression parts.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.12 $ */

public class JmlName extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    /**
     * Construct an <code>ident</code> sort of name or name-suffix.
     * */
    public JmlName( /*@non_null*/TokenReference where, /*@non_null@*/ String ident ) {
	super( where );
	this.sort = SORT_IDENT;
	this.ident = ident;
	this.start = null;
	this.end = null;
	this.name = ident;
    }

    /**
     * Construct a <code>super</code>, <code>this</code>, or 
     * <code>\other</code> sort of name, or a <code>[*]</code> sort of
     * store-ref-name-suffix.
     *
     * <pre><jml>
     * requires sort == SORT_SUPER || sort == SORT_THIS || sort == SORT_ALL 
     *       || sort == SORT_FIELDS || sort == SORT_WILDCARD ;
     * </jml></pre>
     * */
    public JmlName( /*@ non_null */ TokenReference where, int sort ) {
	super( where );
	if (sort == SORT_SUPER) {
	    this.name = "super";
	} else if (sort == SORT_THIS) {
	    this.name = "this";
	} else if (sort == SORT_ALL) {
	    this.name = "[*]";
	} else if (sort == SORT_FIELDS) {
	    this.name = "*";
	} else if (sort == SORT_WILDCARD) {
	    this.name = "*";
	} else {
	    throw new IllegalArgumentException();
	} // end of if 

	this.sort = sort;
	this.ident = null;
	this.start = null;
	this.end = null;
    }

    /**
     * Construct a <code>[ spec-expression ]</code> sort of
     * store-ref-name-suffix.  */
    public JmlName( /*@non_null@*/ TokenReference where, 
		    /*@non_null@*/ JmlSpecExpression start ) {
	super( where );
	this.sort = SORT_POS;
	this.ident = null;
	this.start = start;
	this.end = null;
	this.name = "[]";
    }

    /**
     * Construct a an index-range suffix.
     * These look like <code>[ spec-expression .. spec-expression ]</code>.
     */
    public JmlName( /*@non_null@*/ TokenReference where, 
		    /*@non_null@*/ JmlSpecExpression start, 
		    /*@non_null@*/ JmlSpecExpression end ) {
	super( where );
	this.sort = SORT_RANGE;
	this.ident = null;
	this.start = start;
	this.end = end;
	this.name = "[ .. ]";
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ nullable */ String ident() {
	return ident;
    }

    public /*@non_null@*/ String getName() {
	return name;
    }

    public /*@nullable*/ JmlSpecExpression start() {
	return start;
    }

    public /*@nullable*/ JmlSpecExpression end() {
	return end;
    }

    public boolean isIdent() {
	return sort == SORT_IDENT;
    }

    public boolean isThis() {
	return sort == SORT_THIS;
    }

    public boolean isSuper() {
	return sort == SORT_SUPER;
    }

    public boolean isSpecArrayRefExpr() {
	return sort == SORT_POS || sort == SORT_RANGE || sort == SORT_ALL;
    }

    public boolean isPos() {
	return sort == SORT_POS;
    }

    public boolean isRange() {
	return sort == SORT_RANGE;
    }

    public boolean isAll() {
	return sort == SORT_ALL;
    }
    
    public boolean isFields() {
	return sort == SORT_FIELDS;
    }

    public boolean isWildcard() {
	return sort == SORT_WILDCARD;
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
     * Typechecks the store reference and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this store reference appears
     * @return a desugared store reference
     * @exception PositionedError if the check fails 
     */
    public /*@non_null@*/ JmlName typecheck( 
			      /*@non_null@*/ CExpressionContextType context ) 
	throws PositionedError 
    {
	if (isPos()) {
	    start = (JmlSpecExpression) start.typecheck(context);
	    check(context, start.getType().isOrdinal(),
		  JmlMessages.NOT_INTEGRAL_EXPRESSION, start.getType());
	} else if (isRange()) {
	    start = (JmlSpecExpression) start.typecheck(context);
	    check(context, start.getType().isOrdinal(),
		  JmlMessages.NOT_INTEGRAL_EXPRESSION, start.getType());
	    end = (JmlSpecExpression) end.typecheck(context);
	    check(context, end.getType().isOrdinal(),
		  JmlMessages.NOT_INTEGRAL_EXPRESSION, end.getType());
	} 
	// the rest (super, this, ident, [*], .*) to be checked by the caller

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
	    ((JmlVisitor)p).visitJmlName(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * The sort of store-ref-name or store-ref-name-suffix that
     * this represents.  */
    /*@ private invariant sort == SORT_SUPER || sort == SORT_THIS ||
      @	      sort == SORT_IDENT || sort == SORT_POS ||
      @	      sort == SORT_RANGE || sort == SORT_ALL;
      @*/
    private final int sort;

    private final /*@ nullable */ String ident;

    private /*@ nullable */ JmlSpecExpression start;
    private /*@ nullable */ JmlSpecExpression end;

    public static final int SORT_SUPER = 0;
    public static final int SORT_THIS = 1;
    public static final int SORT_IDENT = 2;
    public static final int SORT_POS = 3;
    public static final int SORT_RANGE = 4;
    public static final int SORT_ALL = 5;
    public static final int SORT_WILDCARD = 6;
    public static final int SORT_FIELDS = 7;

    private final /*@non_null@*/ String name;
}// JmlName
