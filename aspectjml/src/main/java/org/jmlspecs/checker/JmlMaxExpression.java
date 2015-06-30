/*
 * Copyright (C) 2003 Iowa State University
 *
 * This file is part of the JML Project.
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
 * $Id: JmlMaxExpression.java,v 1.1 2003/07/27 11:20:00 davidcok Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlMaxExpression.java
 *
 * @author David R. Cok
 * @version $Revision: 1.1 $
 */

public class JmlMaxExpression extends JmlQuotedExpressionWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlMaxExpression( TokenReference where, 
                                  JExpression expression ) {
	super( where, expression );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ CType getType() {
	return CStdType.Object; // FIXME
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
     * @return a desugared specification expression
     * @exception PositionedError if the check fails */
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError 
    {
	if (!(context instanceof JmlExpressionContext))
	    throw new IllegalArgumentException(
	      "JmlExpressionContext object expected");

	expression = expression.typecheck(context);
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
	    ((JmlVisitor)p).visitJmlMaxExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlMaxExpression
