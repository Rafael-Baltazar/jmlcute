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
 * $Id: JmlLoopStatement.java,v 1.10 2005/08/17 06:14:57 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents loop-stmts annotated with loop-invariants
 * and/or variant-functions.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.10 $ */

public class JmlLoopStatement extends JStatementWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    
    /**
     * Constructs a new instance with the given arguments.
     *
     * <pre><jml>
     * requires (stmt instanceof JLoopStatement) || 
     *          (stmt instanceof JLabeledStatement);
     * requires stmt instanceof JLabeledStatement ==>
     *          ((JLabeledStatement)stmt).stmt() instanceof JLoopStatement;
     * requires loopInvariants != null || variantFunctions != null;
     * </jml></pre>
     */
    public JmlLoopStatement( TokenReference where, 
			     JmlLoopInvariant[] loopInvariants,
			     JmlVariantFunction[] variantFunctions,
			     /*@ non_null @*/ JStatement stmt,
			     JavaStyleComment[] comments ) 
    {
	super( where, comments );
	this.loopInvariants = loopInvariants == null ?
            new JmlLoopInvariant[0] : loopInvariants;
	this.variantFunctions = variantFunctions == null ? 
            new JmlVariantFunction[0] : variantFunctions;
	this.stmt = stmt;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ non_null pure @*/ JmlLoopInvariant[] loopInvariants() {
	return loopInvariants;
    }

    public /*@ non_null pure @*/ JmlVariantFunction[] variantFunctions() {
	return variantFunctions;
    }
    
    /**
     * Returns the statement of this JML loop statement. The returned
     * object is an instance of either JLabeledStatement or
     * JLoopStatement.
     * 
     * <pre><jml>
     * ensures \result instanceof JLabeledStatement ||
     *         \result instanceof JLoopStatement;
     * ensures \result instanceof JLabeledStatement ==>
     *         ((JLabeledStatement)\result).stmt() instanceof JLoopStatement;
     * </jml></pre>
     */
    public /*@ non_null pure @*/ JStatement stmt() {
	return stmt;
    }

    /**
     * Returns true if the statement of this JML loop statement is a
     * labeled statement.
     */
    public /*@ pure @*/ boolean isLabeled() {
	return stmt instanceof JLabeledStatement;
    }

    public /*@ non_null pure @*/ JLoopStatement loopStmt() {
        if (stmt instanceof JLabeledStatement) {
            return (JLoopStatement) ((JLabeledStatement)stmt).stmt();
        } else {
            return (JLoopStatement) stmt;
        }
    }
    
    /**
     * Returns the label if this statement is a labeled loop
     * statement; otherwise, returns null.
     */
    public String label() {
        if (isLabeled()) {
            return ((JLabeledStatement)stmt).getLabel();
        } else {
            return null;
        }
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
     * Typechecks this JML loop statement in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context )
	throws PositionedError 
    {
        // The variables declared within the initializer of a for loop
        // must be visible to the loop invariants and variant
        // functions.  Therefore, for such a case we creates a new
        // context for this; otherwise, we use the given context.
        CFlowControlContextType ctx = context;
        JLoopStatement loopStmt = loopStmt();
        if ((loopStmt instanceof JForStatement) &&
            ((JForStatement)loopStmt).init() 
                instanceof JVariableDeclarationStatement) {
            JVariableDeclarationStatement init =
               (JVariableDeclarationStatement)((JForStatement)loopStmt).init();
            ctx = context.createFlowControlContext(init.getVars().length,
						   getTokenReference());
            init.typecheck( ctx );
        } 

        // typecheck loop invariants and variant functions, if any.
        CExpressionContextType ectx;
        for( int i = 0; i < loopInvariants.length; i++ ) {
            ectx = JmlExpressionContext.createInternalCondition(ctx);
            loopInvariants[i].typecheck( ectx );
//          no support in AspectJML --- [[[hemr]]]
            check(context, 
                    false,
                    JmlMessages.NO_SUPPORT_LOOP_INVARIANT);
        }
        for( int i = 0; i < variantFunctions.length; i++ ) {
            ectx = JmlExpressionContext.createInternalCondition(ctx);
            variantFunctions[i].typecheck( ectx );
//          no support in AspectJML --- [[[hemr]]]
            check(context, 
                    false,
                    JmlMessages.NO_SUPPORT_LOOP_VARIANT);
        }

        // finally, typecheck the Java loop statement in the given context
	stmt.typecheck( context );
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
	//fail( "genCode not yet implemented for loop-stmts" );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlLoopStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@ non_null @*/ JmlLoopInvariant[] loopInvariants;
    private /*@ non_null @*/ JmlVariantFunction[] variantFunctions;

    /*@ private invariant (stmt instanceof JLoopStatement) ||
      @           (stmt instanceof JLabeledStatement);
      @*/

    /*@ private invariant stmt instanceof JLabeledStatement ==>
      @    ((JLabeledStatement)stmt).stmt() instanceof JLoopStatement;
      @*/

    private /*@ non_null @*/ JStatement stmt;
}
