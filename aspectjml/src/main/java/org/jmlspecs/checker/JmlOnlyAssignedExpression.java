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
 * $Id: JmlOnlyAssignedExpression.java,v 1.4 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlOnlyAssignedExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.4 $
 */

public class JmlOnlyAssignedExpression extends JmlStoreRefListWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlOnlyAssignedExpression( /*@non_null*/ TokenReference where,
    		/*@non_null*/JmlStoreRef[] storeRefList ) {
	super( where, storeRefList );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

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
    public /*@non_null@*/ JExpression 
	typecheck(/*@non_null@*/  CExpressionContextType context ) 
	throws PositionedError 
    {
	super.typecheck(context);
	//@ assert (context instanceof JmlExpressionContext);

	// is \only_assigned allowed in this context?
	if (!((JmlExpressionContext) context).notModifiedOk()) {
	    context.reportTrouble(new PositionedError(getTokenReference(),
	       JmlMessages.ONLY_ASSIGNED_NOT_ALLOWED));
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
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlOnlyAssignedExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlOnlyAssignedExpression
