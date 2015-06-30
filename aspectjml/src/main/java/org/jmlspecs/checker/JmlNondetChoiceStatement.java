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
 * $Id: JmlNondetChoiceStatement.java,v 1.5 2005/08/04 05:32:25 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlNondetChoiceStatement.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlNondetChoiceStatement extends JmlModelProgStatement {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlNondetChoiceStatement( TokenReference where,
				     JBlock[] alternativeStatements,
				     JavaStyleComment[] comments ) {
	super( where, comments );
	this.alternativeStatements = alternativeStatements;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------


    /**
     * Returns an array of <code>JStatement</code> arrays, each of
     * them representing a jml-compound-statement.  */
    public JBlock[] alternativeStatements() {
	return alternativeStatements;
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
     * Typechecks this statement in the context in which it
     * appears.  Mutates the context to record the information learned
     * during checking.
     *
     * @param context	the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError 
    {

	CFlowControlContextType	inside = 
	    context.createFlowControlContext(getTokenReference());
	CFlowControlContextType[]	branchContexts = 
	    new CFlowControlContextType[alternativeStatements.length];

	// create a clone of the context for each alternativeStatement so 
	// we can check each in a context that doesn't include the results
	// of checking the others
	for( int i = 0; i < alternativeStatements.length; i++ ) {
	    branchContexts[i] = inside.cloneContext();
	    alternativeStatements[i].typecheck( branchContexts[i] );
	}

	boolean	isFirst = true;

	// based on the information from typechecking the alternativeStatements,
	// reconnect the contexts
	for( int i = 0; i < alternativeStatements.length; i++ ) {
	    if( isFirst && branchContexts[i].isReachable() ) {
		context.adopt( branchContexts[i] );
		isFirst = false;
	    } else if( branchContexts[i].isReachable() ) {
		context.merge( branchContexts[i] );
	    }
	}

	context.checkingComplete();
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
	    ((JmlVisitor)p).visitJmlNondetChoiceStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JBlock[] alternativeStatements;
    // private JStatement[][] alternativeStatements;

}
