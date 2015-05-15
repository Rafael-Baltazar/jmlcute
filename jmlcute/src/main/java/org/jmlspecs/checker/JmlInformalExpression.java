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
 * $Id: JmlInformalExpression.java,v 1.5 2003/06/12 19:52:41 f_rioux Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlInformalExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlInformalExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /** Constructs an instance. The constructed informal description
     * is of type boolean. */
    public JmlInformalExpression( TokenReference where, String text ) {
	this(where, text, true);
    }

    /** Constructs an instance. If the argument <code>isBoolean</code>
     * is true, a boolean-typed informal description is constructed;
     * otherwise, an int-typed one is constructed. */
    private JmlInformalExpression( TokenReference where, String text, 
                                   boolean isBoolean) {
	super( where );
	this.text = text;
        this.isBoolean = isBoolean;
    }

    /** Returns a new informal description of type boolean. */
    public static JmlInformalExpression ofBoolean(TokenReference where, 
                                                  String text) {
        return new JmlInformalExpression(where, text, true);
    }

    /** Returns a new informal description of type int. */
    public static JmlInformalExpression ofInteger(TokenReference where, 
                                                  String text) {
        return new JmlInformalExpression(where, text, false);
    }

    /** Returns a new informal description of type int out of the
        given informal description expression. */
    public static JmlInformalExpression ofInteger(JmlInformalExpression expr) {
        return new JmlInformalExpression(expr.getTokenReference(),
                                         expr.text(), false);
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the text of this informal description. */
    public String text() {
	return text;
    }

    /** Returns the type of this informal description. It is either boolean or
     * int. */
    public CType getType() {
        if (isBoolean) {
            return CStdType.Boolean;
        } else {
            return CStdType.Integer;
        }
    }

    /** Returns true if this is a constant. */
    public /*@ pure @*/ boolean isConstant() {
	return false;
    }

    public JLiteral getLiteral() {
        if (isBoolean) {
            return new JBooleanLiteral(getTokenReference(), true);
        } else {
            return new JOrdinalLiteral(getTokenReference(), 1, 
                                       CStdType.Integer);
        }
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
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError 
    {
	// nothing to check for an informal description
	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlInformalExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * The text of this informal description.  */
    private String text;

    /**
     * Is this informal description of type boolean or int? */
    final private boolean isBoolean;

}
