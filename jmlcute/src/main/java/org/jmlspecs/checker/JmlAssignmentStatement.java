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
 * $Id: JmlAssignmentStatement.java,v 1.2 2005/08/10 06:59:09 cruby Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CodeSequence;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JExpressionStatement;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlAssignmentStatement.java
 *
 * @version $Revision: 1.2 $
 */

public class JmlAssignmentStatement extends JStatementWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlAssignmentStatement( JExpressionStatement assignmentStatement)
    {
	super( assignmentStatement.getTokenReference(), null );
	this.assignmentStatement = assignmentStatement;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the assignment expression of this assignment statement. */
    public /*@ pure @*/ JExpressionStatement assignmentStatement() {
	return assignmentStatement;
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
            assignmentStatement.typecheck(context);
	} catch (PositionedError e) {
	    context.reportTrouble(e);
	}

	JExpression expr = assignmentStatement.expr();

	check(context, 
	      expr instanceof JAssignmentExpression,
	      JmlMessages.SET_STATEMENT);
            
	// Check if the left-hand-side of the assignment
	// expression is a reference to a ghost field
	// It's an error if it is a ghost field.
	check(context, 
	      ! isGhostFieldReference(((JAssignmentExpression)expr).left()),
	      JmlMessages.LHS_OF_ASSIGN_STATEMENT);
    }
    
    /**
     * Returns <code>true</code> if the given expression,
     * <code>expr</code> is a reference to a ghost field.
     */
    public static /*@ pure @*/ boolean isGhostFieldReference(
        JExpression expr) {
        if (expr instanceof JClassFieldExpression) {
            CFieldAccessor field = ((JClassFieldExpression)expr).getField();
            return (field instanceof JmlModifiable) 
                && ((JmlModifiable) field).isGhost();
        } else if (expr instanceof JLocalVariableExpression) {
            JLocalVariable var = ((JLocalVariableExpression)expr).variable();
	    long modifiers = var.modifiers();
	    return hasFlag(modifiers, ACC_GHOST);
        }
        return false;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
	//fail( "code generation not implemented for set-statement" );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlAssignmentStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JExpressionStatement assignmentStatement;

}
