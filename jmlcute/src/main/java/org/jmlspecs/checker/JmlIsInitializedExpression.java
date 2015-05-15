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
 * $Id: JmlIsInitializedExpression.java,v 1.3 2004/03/10 10:15:59 tongjie Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * AST for the JML expression <tt>\is_initialized</tt>. This expression
 * denotes if the argument has finished its static initialization.
 * It is of type <tt>boolean</tt>.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.3 $
 */

public class JmlIsInitializedExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlIsInitializedExpression( TokenReference where, 
				       CType referenceType ) {
	super( where );
	this.referenceType = referenceType;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public CType referenceType() {
	return referenceType;
    }

    public CType getType() {
	return CStdType.Boolean;
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
	//@ assert referenceType != null;

	// can find the named type?
	try {
	   referenceType =  referenceType.checkType( context );
	}
	catch (UnpositionedError e) {
	    throw new PositionedError(getTokenReference(),
				      JmlMessages.TYPE_UNKNOWN,
				      referenceType);
	}

	// class/interface type, i.e., not array type?
	check( context, 
	       !referenceType.isArrayType(),
	       JmlMessages.NOT_CLASS_TYPE,
	       referenceType );

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
	    ((JmlVisitor)p).visitJmlIsInitializedExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ invariant referenceType != null;
    private /*@ spec_public @*/ CType referenceType;

}
