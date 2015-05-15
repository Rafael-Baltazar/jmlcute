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
 * $Id: JmlAssertOrAssumeStatement.java,v 1.8 2006/11/27 15:36:47 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.JavaStyleComment;

/**
 * This class represents the type of assert-statement, and
 * assume-statement in JML.  Note that assert-statement is in the mjc
 * package. The syntax for JML assert/assume statements is defined as
 * follows.
 *
 * <pre>
 *  assert-statement ::= "assert" expression [ ":" expression ] ";"
 *  assert-redundantly-statement ::= "assert_redundantly" predicate
 *     [ ":" expression ] ";"
 *  assume-statement ::= assume-keyword predicate [ ":" expression ] ";"
 *  assume-keyword  ::= "assume" | "assume_redundantly"
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.8 $ */

public abstract class JmlAssertOrAssumeStatement extends JStatementWrapper {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlAssertOrAssumeStatement( TokenReference where,
				       boolean isRedundantly,
				       JmlPredicate predicate,
				       JExpression throwMessage,
				       JavaStyleComment[] comments ) 
    {
	super( where, comments );
	this.isRedundantly = isRedundantly;
	this.predicate = predicate;
	this.throwMessage = throwMessage;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isRedundantly() {
	return isRedundantly;
    }

    public /*@ pure @*/ JmlPredicate predicate() {
	return predicate;
    }

    public /*@ pure @*/ JExpression throwMessage() {
	return throwMessage;
    }
    
    public /*@ pure @*/ boolean hasThrowMessage() {
	return throwMessage != null;
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
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError 
    {
        try {
            enterSpecScope();
            
            // create a new internal condition context 
            JmlExpressionContext ectx = 
                JmlExpressionContext.createInternalCondition( context );

            //@ assert predicate != null;
            predicate = (JmlPredicate) predicate.typecheck(ectx, ACC_PRIVATE);

            if (throwMessage != null) {
                throwMessage = throwMessage.typecheck(ectx);

                // perform purity checks
                JmlExpressionChecker.perform(ectx, throwMessage);
            }
//	    // don't gather nullity information from ass(ert|ume)s
	    context.addFANonNulls(predicate.getFANonNulls(ectx));
	    context.addFANulls(predicate.getFANulls(ectx));
	    
//      no support in AspectJML --- [[[hemr]]]
        check(context, 
                false,
                JmlMessages.NO_SUPPORT_ASSERT_OR_ASSUME_STATEMENT);
        }
        finally {
            exitSpecScope();
        }
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
	//fail( "code generation not implemented for assert" );
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private boolean isRedundantly;

    private JmlPredicate predicate;
    private JExpression throwMessage;
}
