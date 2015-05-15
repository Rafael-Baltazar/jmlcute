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
 * $Id: JmlSpecExpression.java,v 1.16 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CType;
import org.multijava.mjc.CodeSequence;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;

public class JmlSpecExpression extends JExpression 
    implements Cloneable
{


    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlSpecExpression(/*@non_null@*/  JExpression expression ) {
	super( expression.getTokenReference() );
	this.expression = expression;
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public /*@ pure non_null @*/ JExpression expression() {
	return expression;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@ non_null @*/ CType getType() {
	return expression.getType();
    }

    /**
     * Returns true iff the value represented by this expression is non-null
     */
    public /*@pure*/ boolean isNonNull(/*@non_null*/ CContextType context) {
	    return expression.isNonNull(context);
    }
    /**
     * Returns a list of expressions known to be non-null (null) in this context
     */
    public /*@pure non_null*/ Object[] getFANonNulls(/*@non_null@*/ CContextType context) {
	    return expression.getFANonNulls(context);
    }
    public /*@pure non_null*/ Object[] getFANulls(/*@non_null@*/ CContextType context) {
	    return expression.getFANulls(context);
    }

    public /*@ pure non_null  @*/ Object clone() {
	return super.clone();
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

    public void setExpr(/*@ non_null */ JExpression expr){
	expression = expr;
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Checks this JML predicate in the given context and return the
     * expression that results.
     *
     * <pre><jml>
     * also
     *   ensures \result instanceof JmlSpecExpression;
     * </jml></pre>
     *
     */
    public /*@non_null@*/ JExpression typecheck( /*@non_null@*/ CExpressionContextType context ) 
	throws PositionedError
    {
	expression = expression.typecheck( context );
	return this;
    }

    /**
     * Checks this JML predicate in the given context and return the
     * expression that results. Also, performs visibility and
     * purity checks in the specification context of visibility,
     * <code>privacy</code>.
     */
    public /*@non_null@*/ JExpression typecheck( /*@non_null@*/ CExpressionContextType context,
                                  long privacy )
	throws PositionedError
    {
	expression = expression.typecheck( context );

        purityChecked = true;
        JmlExpressionChecker.perform(context, privacy, expression);
	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@non_null@*/  MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlSpecExpression( this );
	else
	    throw new UnsupportedOperationException( JmlNode.MJCVISIT_MESSAGE );
    }

    public void genCode( /*@ non_null */ CodeSequence code ) {
	expression.genCode( code );
    }

    /* by rzakhejm */
    public /*@non_null@*/ String toString() {
    	return expression.toString();
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@non_null@*/ JExpression expression;

    private boolean purityChecked = false;
}
