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
 * $Id: JmlModelProgram.java,v 1.13 2006/09/13 17:42:02 ye-cui Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlModelProgram.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.13 $
 */

public class JmlModelProgram extends JmlSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlModelProgram( TokenReference where, long modifiers,
			    JStatement[] statements ) {
	super( where );
	this.modifiers = modifiers;
	if (hasFlag(modifiers, Constants.ACC_CODE)) {
	    this.modifiers ^= Constants.ACC_CODE; // remove the code modifier
	    this.isCodeSpec = true;
	} else {
	    this.isCodeSpec = false;
	}
	this.statements = statements == null ? new JStatement[0] : statements;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public long modifiers() {
	return modifiers;
    }

    public JStatement[] statements() {
	return statements;
    }

    public boolean isCodeSpec() {
	return isCodeSpec;
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
     * Returns the maximal set of fields that can be assigned to by 
     * this method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public JmlAssignableFieldSet getAssignableFieldSet( JmlSourceMethod method )
    {
	if ( assignableFieldSet != null ) {
	    return assignableFieldSet;
	}

	// traverse the AST and accumulate the assigned fields
	JmlAccumSubclassingInfo accum = new JmlAccumSubclassingInfo();
	for( int i = 0; i < statements.length; i++ ) {
	    statements[i].accept(accum);
	}
	JExpression[] assignedFields = accum.getAssignedFields();
	JExpression[] calledMethods = accum.getCalledMethods();
	
	// create the assignable field set for the model program
	assignableFieldSet = new JmlAssignableFieldSet();
	for( int i = 0; i < assignedFields.length; i++ ) {
	    if (assignedFields[i] instanceof JClassFieldExpression) { 
		JClassFieldExpression fieldExpr 
		    = (JClassFieldExpression)assignedFields[i];
		if (fieldExpr.prefix() instanceof JThisExpression) {
		    CField field = fieldExpr.getField().getField();
		    assignableFieldSet.add(field);
		}
	    }
	}
	for (int i=0; i<calledMethods.length; i++) {
	    JMethodCallExpression methodCall
		    = (JMethodCallExpression)calledMethods[i];
	    if (methodCall.prefix() instanceof JThisExpression) {
		CMethod calledMeth = methodCall.method();
		if (calledMeth instanceof JmlSourceMethod) {
		    JmlMethodDeclaration calledMethDecl 
			= (JmlMethodDeclaration) 
			((JmlSourceMethod)calledMeth).getAST();
		    JmlAssignableFieldSet calledAssignable 
			= calledMethDecl.getAssignableFieldSet();
		    assignableFieldSet.addAll(calledAssignable);
		}
	    }
	}
	return assignableFieldSet;
    }

    /**
     * Typechecks this model program specification in the context in 
     * which it appears. Mutates the context to record the information 
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError
    {
	CFlowControlContextType inside = 
	    context.createFlowControlContext(getTokenReference());

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

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlModelProgram(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private long modifiers;
    private boolean isCodeSpec;

    private JStatement[] statements;

    protected JmlAssignableFieldSet assignableFieldSet = null;

}
