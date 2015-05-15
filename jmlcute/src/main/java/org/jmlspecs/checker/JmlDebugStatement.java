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
 * $Id: JmlDebugStatement.java,v 1.5 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;

/**
 * A concrete AST node class to represent the debug statement of the
 * following form:
 *
 * <pre>
 *  debug-statement ::= "debug" expression ;
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.5 $
 */

public class JmlDebugStatement extends JStatementWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlDebugStatement( /*@ non_null @*/ TokenReference where,
                              /*@ non_null @*/ JExpression expression,
                              /*@ nullable @*/ JavaStyleComment[] comments ) 
    {
	super( where, comments );
	this.expression = expression;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the expression part of this debug statement. */
    public /*@ non_null @*/ JExpression expression() {
        return expression;
    }

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this statement in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( /*@non_null@*/ CFlowControlContextType context ) 
	throws PositionedError 
    {
        try {
            enterSpecScope();
            
            // create a new internal condition context 
            JmlExpressionContext ectx = 
                JmlExpressionContext.createInternalCondition( context );
            expression = (JExpression) expression.typecheck(ectx);

            // check that no model variable is assigned to.
            JmlExpressionChecker.performSideEffectOk(ectx, expression);
//          no support in AspectJML --- [[[hemr]]]
            check(context, 
                    false,
                    JmlMessages.NO_SUPPORT_DEBUG_STATEMENT);
        }
        finally {
            exitSpecScope();
        }
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( /*@ non_null */ CodeSequence code ) {
	// fail( "code generation not implemented for assert" );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlDebugStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /** The expression part of the debug statement. */
    private /*@ non_null @*/ JExpression expression;
}
