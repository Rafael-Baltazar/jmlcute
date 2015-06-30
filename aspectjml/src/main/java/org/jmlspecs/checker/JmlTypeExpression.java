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
 * $Id: JmlTypeExpression.java,v 1.11 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlTypeExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.11 $
 */

public class JmlTypeExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlTypeExpression( /*@ non_null */ TokenReference where, /*@ non_null @*/ CType type ) {
	super( where );
	this.type = type;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ non_null */ CType type() {
	return type;
    }

    /** Returns the static type of this expression.
     * <pre><jml>
     * also
     *   ensures \result == JmlStdType.TYPE;
     * </jml></pre>
     */
    public /*@ non_null @*/ CType getType() {
	return JmlStdType.TYPE;
    }

    /** Return a type suitable for declaring a variable that can hold
     * the result of evaluating this expression at runtime. This
     * method is used by the runtime assertion checker to declare
     * temporary variables. 
     *
     * <pre><jml>
     * also
     *   ensures \result == CStdType.Class;
     * </jml></pre>
     **/
    public /*@ non_null @*/ CType getApparentType() {
        return CStdType.Class;
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
    public /*@ non_null @*/ JExpression typecheck( /*@ non_null @*/ CExpressionContextType context ) 
	throws PositionedError 
    {
	try {
	    type = type.checkType( context );
	}
	catch (UnpositionedError e) {
	    throw new PositionedError(getTokenReference(),
				      JmlMessages.TYPE_UNKNOWN, type);
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
    public void accept( /*@ non_null @*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlTypeExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@ non_null @*/ CType type;

}
