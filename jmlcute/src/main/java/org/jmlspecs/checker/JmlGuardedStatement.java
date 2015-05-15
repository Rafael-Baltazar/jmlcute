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
 * $Id: JmlGuardedStatement.java,v 1.3 2003/03/05 15:55:47 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlGuardedStatement.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.3 $
 */

public class JmlGuardedStatement extends JStatement {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlGuardedStatement( TokenReference where,
				JmlAssumeStatement assumeStatement,
				JStatement[] statements ) 
    {
	super( where, null );
	this.assumeStatement = assumeStatement;
	this.statements = statements;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlAssumeStatement assumeStatement() {
	return assumeStatement;
    }

    public JStatement[] statements() {
	return statements;
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
	CFlowControlContextType inside = 
	    context.createFlowControlContext(getTokenReference());

	try {
	    assumeStatement.typecheck( inside );
	} catch( CLineError le ) {
	    context.reportTrouble( le );
	}

	for( int i = 0; i < statements.length; i++ ) {
	    if( !inside.isReachable() ) {
		throw new CLineError( statements[i].getTokenReference(), 
				      MjcMessages.STATEMENT_UNREACHABLE );
	    }

	    try {
		statements[i].typecheck( inside );
	    } catch( CLineError le ) {
		context.reportTrouble( le );
	    }
	}

	inside.checkingComplete();
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
	fail( "genCode not yet implemented for guarded-statement" );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlGuardedStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JmlAssumeStatement assumeStatement;
    private JStatement[] statements;

}
