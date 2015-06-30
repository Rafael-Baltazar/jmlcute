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
 * $Id: JmlSpecBody.java,v 1.19 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlSpecBodyClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.19 $
 */

/**
 * An abstraction of JML specification bodies. JML has several differnt
 * forms of specification bodies, and this abstract class is the common
 * superclass of different types of specification bodies, e.g.,
 * JmlAbruptSpecBody, JmlExceptionalSpecBody, JmlGenericSpecBody, 
 * and JmlNormalSpecBody. A particular kind of specification
 * body has the following typical form of production rule:
 *
 * <pre>
 *  X-spec-body :: = measured_clause ...... signals_clause
 *    | "{|" X-spec-case-seq "|}"
 *  X-spec-case-seq := X-spec-case [ "also" X-spec-case ]
 * </pre>
 *
 * where <tt>X<tt> can be <tt>generic</tt>, <tt>normal</tt>, 
 * <tt>exceptional</tt>, etc. The allowed specification body clauses 
 * depend on the type of specification body.
 * 
 * @author Yoonsik Cheon
 * @version $Revision: 1.19 $
 */
public abstract class JmlSpecBody extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specClauses != null && specClauses.length > 0;
    protected JmlSpecBody( /*@ non_null */ JmlSpecBodyClause[] specClauses ) {
	super( specClauses[0].getTokenReference() );
	this.specClauses = specClauses;
	this.specCases = null;
    }

    //@ requires specCases != null && specCases.length > 0;
    protected JmlSpecBody( JmlGeneralSpecCase[] specCases ) {
	super( specCases[0].getTokenReference() );
	this.specClauses = null;
	this.specCases = specCases;
    }

    protected JmlSpecBody( TokenReference where ) {
	super( where );
	this.specClauses = null;
	this.specCases = null;
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /**
     * Returns the maximal set of fields that can be assigned to by 
     * the given method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public JmlAssignableFieldSet getAssignableFieldSet( JmlSourceMethod method )
    {
	if ( assignableFieldSet != null ) {
	    return assignableFieldSet;
	}
	assignableFieldSet = new JmlAssignableFieldSet();
	if ( method.isPure() && !method.isConstructor() ) {
	    return assignableFieldSet;
	}
	boolean hasAssignableClause = false;
	JmlAssignableFieldSet nextSet;
	if (specClauses != null) {
	    for (int i = 0; i < specClauses.length; i++) {
                if ( specClauses[i] instanceof JmlAssignableClause ) {
		    nextSet = ((JmlAssignableClause)specClauses[i])
			.getAssignableFieldSet(method);
		    hasAssignableClause = true;
		    assignableFieldSet.addAll( nextSet );
		}
	    }
	}

	if (specCases != null) {
	    for (int i = 0; i < specCases.length; i++) {
		nextSet = specCases[i].getAssignableFieldSet(method);
                if ( nextSet != null ) {
		    // the "code_contract" has no assignable clause
		    // and therefore returns null
		    hasAssignableClause = true;
		    assignableFieldSet.addAll( nextSet );
		}
	    }
	}

	if ( ! hasAssignableClause ) {
	    assignableFieldSet.setNotSpecified();
	}
	return assignableFieldSet;
    }

    /**
     * Returns the minimal set of fields that can be assigned to by 
     * the given method (takes the intersection of the assignable clauses of 
     * all specification cases). This set is used in the checking of 
     * assignable fields when there are calls in the method body.  
     */
    public JmlAssignableFieldSet getMinAssignableFieldSet( 
					  JmlSourceMethod method, 
					  JmlDataGroupMemberMap dataGroupMap )
    {
	if ( minAssignableFieldSet != null ) {
	    return minAssignableFieldSet;
	}
	if (specClauses != null) {
	    minAssignableFieldSet = getAssignableFieldSet( method );
	    return minAssignableFieldSet;
	}
	if (specCases != null) {
	    JmlAssignableFieldSet nextSet;
	    minAssignableFieldSet = specCases[0].getAssignableFieldSet(method);
	    for (int i = 1; i < specCases.length; i++) {
		nextSet = specCases[i].getAssignableFieldSet(method);
		minAssignableFieldSet 
		    = minAssignableFieldSet.intersect(nextSet, dataGroupMap);
	    }
	}
	return minAssignableFieldSet;
    }

    public boolean isSpecClauses() {
	return specClauses != null;
    }

    public boolean isSpecCases() {
	return specCases != null;
    }

    public boolean hasNonRedundantEnsures() {
	if (specClauses != null) {
	    for (int i = 0; i<specClauses.length; i++) {
		if (specClauses[i] instanceof JmlEnsuresClause
                    && !specClauses[i].isRedundantly()) {
		    return true;
		}
	    }
	}

 	if (specCases != null) {
 	    for (int i = 0; i < specCases.length; i++) {
 		if (specCases[i].hasNonRedundantEnsures()) {
                    return true;
		}
	    }
 	}
	return false;
    }

    public JmlSpecBodyClause[] specClauses() {
	return specClauses;
    }
    
    public JmlGeneralSpecCase[] specCases() {
	return specCases;
    }

    /**
     * Returns true if this general specification case has a non-redunant
     * assignable clause.
     */
    public /*@ pure @*/ boolean hasNonRedundantAssignable() {
	if (specClauses != null) {
	    for (int i = 0; i < specClauses.length; i++) {
                if ((specClauses[i] instanceof JmlAssignableClause) &&
                    !specClauses[i].isRedundantly()) {
                    return true;
		}
	    }
	}

 	if (specCases != null) {
 	    for (int i = 0; i < specCases.length; i++) {
 		if (specCases[i].hasNonRedundantAssignable()) {
                    return true;
		}
	    }
 	}

        return false;
    }

    //---------------------------------------------------------------------
    // Visitors
    //---------------------------------------------------------------------

        public void accept(/*@non_null@*/ MjcVisitor m) {
		((JmlVisitor)m).visitJmlSpecBody(this);
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
     * Typechecks this spec body in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context, long privacy )
	throws PositionedError
    {
	if (specClauses != null) {
	    for (int i = 0; i < specClauses.length; i++) {
		// This try block allows us to display errors from more than 
		// one clause 
		try {
		    specClauses[i].typecheck(context, privacy);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }
	}

	if (specCases != null) {
	    for (int i = 0; i < specCases.length; i++) {
		// This try block allows us to display errors from more than 
		// one clause 
		try {
		    // the third parameter says that this is a nested
		    // spec case sequence
		    specCases[i].typecheck(context, privacy, true);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }
	}
    }


    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ invariant specClauses != null ==> specClauses.length > 0;
    //@ invariant specCases != null ==> specCases.length > 0;
    /*@ invariant (specClauses == null && specCases != null) ||
      @             (specClauses != null && specCases == null);
      @*/
    protected /*@ nullable */ JmlSpecBodyClause specClauses[];
    protected /*@ nullable */ JmlGeneralSpecCase specCases[];
    protected /*@ nullable */ JmlAssignableFieldSet assignableFieldSet = null;
    protected /*@ nullable */ JmlAssignableFieldSet minAssignableFieldSet = null;
}
