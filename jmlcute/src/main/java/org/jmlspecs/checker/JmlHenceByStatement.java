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
 * $Id: JmlHenceByStatement.java,v 1.6 2005/08/19 05:12:16 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlHenceByStatement.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.6 $
 */

public class JmlHenceByStatement extends JStatementWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlHenceByStatement( TokenReference where, boolean isRedundantly,
				JmlPredicate predicate, 
				JavaStyleComment[] comments ) 
    {
	super( where, comments );
	this.isRedundantly = isRedundantly;
	this.predicate = predicate;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isRedundantly() {
	return isRedundantly;
    }

    public JmlPredicate predicate() {
	return predicate;
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

    public void typecheck( CFlowControlContextType context )
	throws PositionedError
    {
        try {
            enterSpecScope();
            CExpressionContextType ectx 
		= JmlExpressionContext.createInternalCondition(context);
            predicate = (JmlPredicate) predicate.typecheck( ectx );
        }
        finally {
            exitSpecScope();
        }
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
	//fail( "genCode is not yet implemented for hence-by-statement" );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlHenceByStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private boolean isRedundantly;
    private JmlPredicate predicate;
}
