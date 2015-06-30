/*
 * Copyright (C) 2006, DSRG, Concordia University 
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
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
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;


/**
 * JmlCastExpression.java
 *
 * This class represents a cast expression such as 
 *     /*@(non_null)* /   o
 *     /*@(non_null T)* / o
 *     (/*@non_null* / T) o
 *
 * @author Perry James
 * @version $Revision: 1.2 $
 */
public class JmlCastExpression extends JCastExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a node in the parsing tree.
     * This method is directly called by the parser.
     * @param	where	the line of this node in the source code
     * @param	expr	the expression to be cast
     * @param	dest	the type of this expression after cast
     */
    public JmlCastExpression( /*@non_null*/ TokenReference where, 
			      /*@non_null*/ JExpression expr, /*@non_null*/ CType dest) {
	super( where, expr, dest );
	this.isExplicitNonNull=false;
    }

    /**
     * Constructs a node in the parsing tree.
     * This method is directly called by the parser.
     * @param	where	the line of this node in the source code
     * @param	expr	the expression to be casted
     * @param	dest	the type of this expression after cast
     * @param	isExplicitNonNull true iff the cast contains a non-null annotation
     */
    public JmlCastExpression( /*@non_null*/ TokenReference where, 
			      /*@non_null*/ JExpression expr, /*@non_null*/ CType dest, 
			      boolean isExplicitNonNull) {
	super( where, expr, dest );
	this.isExplicitNonNull=isExplicitNonNull;
    }

    /**
     * Constructs a node in the parsing tree.  
     * This method is directly called by the parser.
     * The destination type is taken to be the statically determined type of 
     * expr.
     * @param	where	the line of this node in the source code
     * @param	expr	the expression to be casted
     * @param	isExplicitNonNull true iff the cast contains a non-null annotation
     */
    public JmlCastExpression( /*@non_null*/ TokenReference where, 
			      /*@non_null*/ JExpression expr, boolean isExplicitNonNull) {
	super( where, expr, null );
	this.isExplicitNonNull=isExplicitNonNull;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    public /*@non_null*/ String toString() {
	return "(" + 
		(isExplicitNonNull ? "non_null" : "") + 
		(isExplicitNonNull && dest!=null ? " " : "") + 
		(dest==null ? "" : dest.toString()) + 
	       ") " + expr.toString();
    }


    /**
     * Compute the type of this expression.
     *
     * @return the type of this expression
     */
    public /*@non_null*/ CType getType() {
	if (dest==null) {
	   return expr.getType();
	}
	else {
           return super.getType();
	}
    }

    /**
     * Returns true iff the value represented by this expression is non-null
     */
    public /*@pure*/ boolean isNonNull(/*@non_null@*/ CContextType context) {
	return isExplicitNonNull || super.isNonNull(context);
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return  a desugared Java expression (see <code>JExpression.typecheck()</code>)
     * @exception PositionedError if the check fails
     *
     * WMD: issue a warning if there is a downcast from readonly to peer
     * or rep.
     */
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError {
	expr = expr.typecheck( context );

        if (dest==null) {
	   dest=expr.getType();
	}
	   
        return typecheckHelper( context );
    }


    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    protected boolean	isExplicitNonNull;
}
