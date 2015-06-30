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
 * $Id: JmlSpecification.java,v 1.14 2006/09/13 17:42:02 ye-cui Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlSpecification.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.14 $
 */

/** 
 * A class representing JML method specifications without conjoinable
 * specifications. In a non-conjoinable specification, the inherited
 * specifications are "also" extended.  The production rule for
 * non-conjoinable specifications, <tt>specification</tt> is defined
 * as follows.
 *
 * <pre>
 *  specification ::= spec-case-seq [ redundant-spec ]
 *    | redundant-spec
 *  spec-case-seq ::= spec-case [ "also" spec-case ] ...
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.14 $ */

public class JmlSpecification extends JmlMethodSpecification {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    public JmlSpecification( TokenReference where, 
			     JmlSpecCase[] specCases,
			     JmlRedundantSpec redundantSpec)
    {
	super( where, redundantSpec );
	this.specCases = specCases;
    }

    public JmlSpecification( TokenReference where, 
			     JmlRedundantSpec redundantSpec)
    {
	super( where, redundantSpec );
	this.specCases = null;
    }
/*
    // requires redundantSpec != null;
    public JmlSpecification( TokenReference where,
			     JmlRedundantSpec redundantSpec)
    {
	this( where, null, redundantSpec );
    }
*/
    public JmlSpecification newInstance(
				 JmlSpecCase[] specCases,
				 JmlRedundantSpec redundantSpec)
    {
	return new JmlSpecification(getTokenReference(),
				    specCases,
				    redundantSpec);
    }
 
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public boolean hasSpecCases() {
	return specCases != null;
    }
    
    public JmlSpecCase[] specCases() {
	return specCases;
    }

    public JmlRedundantSpec redundantSpec() {
	return redundantSpec;
    }

    //---------------------------------------------------------------------
    // VISITOR
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlSpecification( this );
	else
	    super.accept( p );
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
     * the given method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public JmlAssignableFieldSet getAssignableFieldSet( JmlSourceMethod method )
    {
	if ( assignableFieldSet != null ) {
	    return assignableFieldSet;
	}
	JmlAssignableFieldSet nextSet;
	if (specCases != null) {
	    assignableFieldSet = new JmlAssignableFieldSet();
	    for (int i = 0; i < specCases.length; i++) {
		nextSet = specCases[i].getAssignableFieldSet( method );
		assignableFieldSet.addAll( nextSet );
	    }
	} else {
	    assignableFieldSet = new JmlAssignableFieldSet();
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
	if (specCases != null) {
	    JmlAssignableFieldSet nextSet;
	    minAssignableFieldSet = specCases[0].getAssignableFieldSet(method);
	    for (int i = 1; i < specCases.length; i++) {
		nextSet = specCases[i].getAssignableFieldSet(method);
		minAssignableFieldSet 
		    = minAssignableFieldSet.intersect(nextSet, dataGroupMap);
	    }
	} else {
	    minAssignableFieldSet = new JmlAssignableFieldSet();
	    minAssignableFieldSet.setNotSpecified();
	}
	return minAssignableFieldSet;
    }

    /**
     * Typechecks this <tt>extendingSpecification</tt> in the context 
     * in which it appears. Mutates the context to record the information
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError
    {
	if (specCases != null) {
	    for (int i = 0; i < specCases.length; i++) {
		if (!(specCases[i] instanceof JmlModelProgram)) {
		    specCases[i].typecheck(context);
		}
	    }
	}

	// check redudant specs if any
	super.typecheck( context );
    }

    /**
     * Typechecks the model programs in this
     * <tt>extendingSpecification</tt> in the context in which they
     * appear. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheckModelPrograms( CFlowControlContextType context ) 
	throws PositionedError
    {
	if (specCases != null) {
	    for (int i = 0; i < specCases.length; i++) {
		if (specCases[i] instanceof JmlModelProgram) {
		    specCases[i].typecheck(context);
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

    protected JmlSpecCase specCases[];

    protected JmlAssignableFieldSet assignableFieldSet = null;
    protected JmlAssignableFieldSet minAssignableFieldSet = null;

} // JmlSpecification
