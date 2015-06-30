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
 * $Id: JmlOldExpression.java,v 1.4 2005/08/17 06:14:57 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlOldExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.4 $
 */

public class JmlOldExpression extends JmlSpecExpressionWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlOldExpression( TokenReference where, 
			     JmlSpecExpression specExpression,
			     String label ) {
	super( where, specExpression );
	this.label = label;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ CType getType() {
	return specExpression.getType();
    }

    public String label() { return label; }

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
	if (!(context instanceof JmlExpressionContext)) {
	    throw new IllegalArgumentException(
	      "JmlExpressionContext object expected");
	}

	// is old expression allowed in this context?
	if (!((JmlExpressionContext) context).oldOk()) {
	    context.reportTrouble(new PositionedError(getTokenReference(),
	       JmlMessages.OLD_NOT_ALLOWED));
	}

	// create a new old expression context 
	JmlExpressionContext ectx = 
	    JmlExpressionContext.createOldExpression( 
	        context.getFlowControlContext());

	specExpression = 
	    (JmlSpecExpression) specExpression.typecheck(ectx);

	/* !FIXME! type checking of labels in \old expressions
	 *  requires a separate name space or lookup method;
	 *  the lookup used below does not work because labels 
	 *  have different scope rules than they do in continue 
	 *  and break statements.
	if( label != null ) {
	    target = context.
		getFlowControlContext().getLabeledStatement( label );
	    check( context, target != null, 
		   JmlMessages.LABEL_UNKNOWN, label );
	}
	*/
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
	    ((JmlVisitor)p).visitJmlOldExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private String 		label;
    private JStatement		target;
}// JmlOldExpression
