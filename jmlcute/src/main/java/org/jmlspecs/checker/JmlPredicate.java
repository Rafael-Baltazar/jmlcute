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
 * $Id: JmlPredicate.java,v 1.12 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.CodeSequence;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;

/**
 * This represents the AST node for a predicate in JML.  */
public class JmlPredicate extends JExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlPredicate( /*@ non_null @*/ JmlSpecExpression specExpression ) {
	super( specExpression.getTokenReference() );
	this.specExpression = specExpression;
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isSameKeyword() {
	return false;
    }

    public /*@ pure non_null @*/ JmlSpecExpression specExpression() {
	return specExpression;
    }

    public /*@ pure non_null @*/ CType getType() {
	return CStdType.Boolean;
    }

    /** Returns true if the purity of this spec expression has already
     * been performed. */
    public /*@ pure @*/ boolean purityChecked() {
        return purityChecked;
    }

    /** Indicates the the purity of this spec expression has already
     * been performed. */
    public void setPurityChecked() {
        purityChecked = true;
    }
    
    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@ non_null @*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlPredicate( this );
	else
	    throw new UnsupportedOperationException( JmlNode.MJCVISIT_MESSAGE );
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    /**
     * Returns true iff the value represented by this expression is non-null
     */
    public /*@pure*/ boolean isNonNull(/*@non_null@*/ CContextType context) {
	    return specExpression.isNonNull(context);
    }

    /**
     * Returns a list of expressions known to be non-null (null) in this context
     */
    public /*@pure non_null*/ Object[] getFANonNulls(/*@non_null@*/ CContextType context) {
	    return specExpression.getFANonNulls(context);
    }
    public /*@pure non_null*/ Object[] getFANulls(/*@non_null@*/ CContextType context) {
	    return specExpression.getFANulls(context);
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this JML predicate in the context of the given
     * context, <code>context</code>. Also, performs visibility and
     * purity checks in the specification context of visibility,
     * <code>privacy</code>.
     *
     * <pre><jml>
     * requires context != null;
     * </jml></pre>
     */
    public /*@ non_null @*/ JExpression typecheck( /*@ non_null @*/ CExpressionContextType context,
                                  long privacy )
	throws PositionedError
    {
        purityChecked = true;
	specExpression = 
	    (JmlSpecExpression) specExpression.typecheck( context, privacy );
	check( context, specExpression.getType().equals(CStdType.Boolean),
	       JmlMessages.NOT_BOOLEAN );
	return this;
    }

    /**
     * Typechecks this JML predicate in the context of the given
     * context, <code>context</code>.
     */
    public /*@ non_null @*/ JExpression typecheck(/*@ non_null @*/ CExpressionContextType context ) 
	throws PositionedError
    {
	specExpression = 
	    (JmlSpecExpression) specExpression.typecheck( context );
	check( context, specExpression.getType().equals(CStdType.Boolean),
	       JmlMessages.NOT_BOOLEAN );
	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode(/*@non_null@*/ CodeSequence code ) {
	specExpression.genCode( code );
    }

    /* by rzakhejm */
    public /*@non_null@*/ String toString() {
	return specExpression().toString();
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@ non_null @*/ JmlSpecExpression specExpression;

    private boolean purityChecked = false;
}
