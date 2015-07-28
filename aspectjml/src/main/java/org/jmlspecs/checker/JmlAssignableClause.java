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
 * $Id: JmlAssignableClause.java,v 1.19 2006/12/20 06:16:00 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;

/**
 * A JML AST node for the <code>assignable</code> clause.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.19 $
 */

public class JmlAssignableClause extends JmlSpecBodyClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires storeRefs != null && storeRefs.length > 0;
    public JmlAssignableClause( /*@ non_null */ TokenReference where,
				boolean isRedundantly, 
				/*@ non_null */ JmlStoreRef storeRefs[] ) {
		super( where, isRedundantly );
		this.storeRefs = storeRefs;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //@ pure
    public int preferredOrder() {
    	return PORDER_ASSIGNABLE_CLAUSE;
    }

    public /*@ non_null */ JmlStoreRef[] storeRefs() {
    	return storeRefs;
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

    public void precheckStoreRefs(/*@ non_null @*/ JmlSourceClass methodOwner )
    {
		// this is only necessary to handle the rare cases when 
		// a super type and subtype are in the same file 
		// and would have been checked in the wrong order.  
		// This only seems to occur in the test cases 
		// rather than in practice.
		// !FIXME! should probably give a warning that the 
		// checking will not be complete (only fields of the
		// receiver).  
		fieldSet = new JmlAssignableFieldSet();
		CExpressionContextType dummyContext 
		    = new CExpressionContext( 
			      JmlContext.createDummyContext(methodOwner) );
		for (int i=0; i<storeRefs.length; i++) {
		    JmlStoreRef storeRef = storeRefs[i];
		    if ( storeRef.isFieldOfReceiver() ) {
			try {
			    // data groups are model fields
			    JmlContext.enterSpecScope();
	
			    JmlName[] names = ((JmlStoreRefExpression)storeRef).names();
			    String name = names[names.length-1].ident();
			    CField field = (JmlSourceField)
				methodOwner.lookupFieldHelper(name, dummyContext);
			    if (field != null) {
				// has been typechecked
				fieldSet.add(field);
			    }
			} catch (UnpositionedError e) {
			    dummyContext.reportTrouble(
				new PositionedError( 
				        storeRef.getTokenReference(),
				        e.getFormattedMessage() )
				);
			}
			finally{
			    JmlContext.exitSpecScope();
			}
		    } else if (storeRef instanceof JmlStoreRefKeyword) {
			fieldSet.add(storeRefs[i]);
		    }
		}
    }
    
    public /*@ non_null */ JmlAssignableFieldSet getAssignableFieldSet(/*@ non_null @*/ JmlSourceMethod method )
    {
		if ( fieldSet != null ) {
		    return fieldSet;
		}
		if ( ! finishedTypeChecking ) {
		    precheckStoreRefs( (JmlSourceClass)method.owner() );
		    return fieldSet;
		}
		return getAssignableFieldSet();
    }
    
    public /*@ non_null */ JmlAssignableFieldSet getAssignableFieldSet() {
		if ( fieldSet != null ) {
		    return fieldSet;
		}
	
		fieldSet = new JmlAssignableFieldSet();
		for (int i=0; i<storeRefs.length; i++) {
		    fieldSet.add(storeRefs[i]);
		}
		return fieldSet;
    }

    /**
     * Typechecks this <code>assignable</code> clause in the context
     * in which it appears. Mutates the context to record the
     * information learned during checking.
     *
     * @param context the context in which this appears
     * @param privacy the visibility level with which to typecheck
     * @exception PositionedError if any checks fail */
    public void typecheck(/*@ non_null @*/ CFlowControlContextType context, long privacy )
	throws PositionedError
    {
	    boolean isPure = true;
		for (int i = 0; i < storeRefs.length; i++) {
		    // create a new precondition expression context 
		    JmlExpressionContext ectx = 
			JmlExpressionContext.createPrecondition( context );
	
		    //@ assert storeRefs[i] != null;
		    storeRefs[i] = storeRefs[i].typecheck(ectx, privacy);
	
		    JmlStoreRef storeRef = storeRefs[i];
	
		    if ( storeRef.isInvalidModelFieldRef() ) {
			context.reportTrouble(
				    new PositionedError(
			                  storeRefs[i].getTokenReference(), 
					  JmlMessages.INVALID_MODEL_FIELD_IN_ASSIGNABLE,
					  storeRef.toString())
				    );
		    }
	
		    // 'this' and 'super' are not allowed in the assignable clause.
		    // needs to be an assignable field, 
		    // e.g., this.x, super.x, or (for all fields of this) this.*
		    if ( storeRef.isThisExpression() ) {
			context.reportTrouble(
				    new PositionedError(
			                    storeRefs[i].getTokenReference(), 
					    JmlMessages.RECEIVER_IN_ASSIGNABLE,
				            "this")
				    );
		    }
		    if ( storeRef.isSuperExpression() ) {
			context.reportTrouble(
				    new PositionedError(
			                    storeRefs[i].getTokenReference(), 
					    JmlMessages.RECEIVER_IN_ASSIGNABLE,
				            "super")
				    );
		    }
	
	            isPure = isPure 
			     // local variables can be changed without affecting 
			     // the purity of a method (occurs in model programs)
			&& ( storeRefs[i].isNothingOrNotSpecified()
			     || storeRefs[i].isLocalVarReference() );
		}
	        
	        // is the current method pure?
	        if (!context.getCMethod().isConstructor() &&
	            methodPureness(context.getCMethod()) == 1) { 
	            check(context, isPure, JmlMessages.PURE_AND_ASSIGNABLE);
	        }
		finishedTypeChecking = true;
    }


    /**
     * Returns 1 if the given method, <code>meth</code>, is a pure
     * method. A method is pure if it is annotated with the JML
     * <code>pure</code> modifier or its owner (a class or an
     * interface) is declared as pure. Returns -1 if the given method
     * is not pure; returns 0 if it can not be determined, e.g., no
     * source code is available.
     */
    public int methodPureness(/*@ non_null @*/ CMethod meth) {
        if (meth instanceof JmlSourceMethod) {
        	return ((JmlSourceMethod)meth).isPure() ? 1 : -1;
        }
        return 0;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept(/*@ non_null @*/ MjcVisitor p ) {
		if (p instanceof JmlVisitor)
		    ((JmlVisitor)p).visitJmlAssignableClause(this);
		else
		    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant storeRefs != null && storeRefs.length > 0;
    private /*@ non_null */ JmlStoreRef[] storeRefs;
    private /*@ nullable */ JmlAssignableFieldSet fieldSet = null;

    private boolean finishedTypeChecking = false;
}
