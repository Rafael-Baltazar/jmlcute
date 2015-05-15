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
 * $Id: JmlMethodSpecification.java,v 1.26 2006/12/20 06:16:01 perryjames Exp $
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
 * @version $Revision: 1.26 $
 */

abstract public class JmlMethodSpecification extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    public JmlMethodSpecification( /*@ non_null*/ TokenReference where ) {
	this ( where, null );
    }

    public JmlMethodSpecification( /*@ non_null*/ TokenReference where, 
    		/*@ nullable*/ JmlRedundantSpec redundantSpec) {
	super ( where );
	this.redundantSpec = redundantSpec;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public boolean hasSpecCases() {
	return false;
    }
    
    public /*@ nullable @*/ JmlSpecCase[] specCases() {
	return null;
    }

    public /*@ non_null*/ JmlRedundantSpec redundantSpec() {
	return redundantSpec;
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
    public abstract /*@non_null@*/ JmlAssignableFieldSet getAssignableFieldSet(
					   /*@non_null@*/ JmlSourceMethod method );

    /**
     * Returns the minimal set of fields that can be assigned to by 
     * the given method (takes the intersection of the assignable clauses of 
     * all specification cases). This set is used in the checking of 
     * assignable fields when there are calls in the method body.  
     */
    public abstract 
	/*@ non_null */ JmlAssignableFieldSet getMinAssignableFieldSet(
					  /*@non_null@*/ JmlSourceMethod method, 
					  /*@non_null@*/ JmlDataGroupMemberMap dataGroupMap );

    /**
     * Typechecks this <code>methodSpecification</code> in the context 
     * in which it appears. Mutates the context to record the information
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( /*@non_null@*/ CFlowControlContextType context ) 
	throws PositionedError
    {
	if (redundantSpec != null)
	    redundantSpec.typecheck(context);
    }

    /**
     * Typechecks the model programs in this
     * <tt>extendingSpecification</tt> in the context in which they
     * appear. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public abstract void typecheckModelPrograms(/*@non_null@*/ CFlowControlContextType context) 
	throws PositionedError;

    /** Returns the privacy, access modifier, of the current method
     * being typechecked. If the method has either SPEC_PUBLIC or
     * SPEC_PROTECTED modifier, then it takes a precedence over the
     * JAVA access modifiers. */
    private long privacy( /*@non_null@*/ CFlowControlContextType context ) {
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

    public void accept(/*@non_null@*/ MjcVisitor m) {
             ((JmlVisitor)m).visitJmlMethodSpecification(this);
     }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /** Redundant specification such as examples */
    protected /*@ nullable */ JmlRedundantSpec redundantSpec;
    
}
