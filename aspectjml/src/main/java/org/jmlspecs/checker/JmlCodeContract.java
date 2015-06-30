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
 * $Id: JmlCodeContract.java,v 1.6 2006/09/13 17:42:01 ye-cui Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * An abstraction of JML method specification. This is the common 
 * superclass of various JML method specifications. The redudant
 * specification and the subclass contract specification are allowed 
 * in all variations, thereby they are defined here. The production
 * rule for method specifications, <tt>method-specification</tt> is
 * defined as follows.
 *
 * <pre>
 *  method-specification ::= specification | extending-specification
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.6 $
 */

public class JmlCodeContract extends JmlSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    public JmlCodeContract( TokenReference where ) {
	this ( where, 
	       0,
	       new JmlAccessibleClause[0],
	       new JmlCallableClause[0],
	       new JmlMeasuredClause[0] );
    }

    public JmlCodeContract( TokenReference where, 
			    long privacy,
			    JmlAccessibleClause[] accessibleClauses,
			    JmlCallableClause[] callableClauses,
			    JmlMeasuredClause[] measuredClauses)
    {
	super ( where );
	this.privacy = privacy;
	this.accessibleClauses = accessibleClauses;
	this.callableClauses = callableClauses;
	this.measuredClauses = measuredClauses;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------
    public JmlAccessibleClause[] accessibleClauses() {
	return accessibleClauses;
    }
    public JmlCallableClause[] callableClauses() {
	return callableClauses;
    }
    public JmlMeasuredClause[] measuredClauses() {
	return measuredClauses;
    }

    /**
     * Returns an empty set since there are no assignable clauses in 
     * the "code_contract".
     */
    public JmlAssignableFieldSet getAssignableFieldSet( JmlSourceMethod method )
    {
	return null;
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
     * Typechecks this <code>CodeContract</code> in the context 
     * in which it appears. Mutates the context to record the information
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError
    {
	/*
	if (callableClauses.length > 0 || accessibleClauses.length > 0 ) {

	    // check if the method is public or protected
	    if (!hasFlag(privacy(context), ACC_PUBLIC | ACC_SPEC_PUBLIC |
			 ACC_PROTECTED | ACC_SPEC_PROTECTED)) {
		context.reportTrouble(new CWarning(
					  getTokenReference(),
                                          JmlMessages.SUBCLASSING_CONTRACT));
	    }
	}
	 */

	// check each accessible clause with protected visibility
	for (int i = 0; i < accessibleClauses.length; i++) {
	    accessibleClauses[i].typecheck(context, privacy);
	}

	// check each callable clause with protected visibility
	for (int i = 0; i < callableClauses.length; i++) {
	    callableClauses[i].typecheck(context, privacy);
	}

	// check each measured_by clause with the visibility of the context
	for (int i = 0; i < measuredClauses.length; i++) {
	    measuredClauses[i].typecheck(context, privacy);
	}
    }

    /** Returns the privacy, access modifier, of the current method
     * being typechecked. If the method has either SPEC_PUBLIC or
     * SPEC_PROTECTED modifier, then it takes a precedence over the
     * JAVA access modifiers. */
    private long privacy( CFlowControlContextType context ) {
        //@ assert context.getCMethod() != null;
        long modifiers = context.getCMethod().modifiers();
        long privacy = modifiers & (ACC_SPEC_PUBLIC | ACC_SPEC_PROTECTED);
        if (privacy == 0) {
            privacy =  modifiers & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE);
        }
        return privacy;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

     public void accept(MjcVisitor m) {
             ((JmlVisitor)m).visitJmlCodeContract(this);
     }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ private invariant privacy == 0 ||
      @    privacy == Constants.ACC_PUBLIC ||
      @    privacy == Constants.ACC_PROTECTED ||
      @    privacy == Constants.ACC_PRIVATE;
      @*/
    private long privacy;

    /** The accessible clauses from the specification */
    protected JmlAccessibleClause accessibleClauses[];

    /** The callable clauses from the specification */
    protected JmlCallableClause callableClauses[];

    /** The measured_by clauses from the specification */
    protected JmlMeasuredClause measuredClauses[];
}
