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
 * $Id: JmlGeneralSpecCase.java,v 1.19 2006/12/11 05:59:03 chalin Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;

/**
 * An abstraction of JML specification cases. JML supports several 
 * kinds of specification cases, and this abstract class is the common
 * superclass of different kinds of specification cases such as
 * normal, exceptional, and generic (i.e., JmlExceptionalSpecCase, 
 * JmlNormalSpecCase, and JmlGenericSpecCase). A particular kind of 
 * specification case has the following form of production rule:
 *
 * <pre>
 *  X-spec-case :: = [ spec-var-decls ] spec-header [ X-spec-body ]
 *    | [ spec-var-decls ] X-spec-body
 * </pre>
 *
 * where <tt>X<tt> can be <tt>generic</tt>, <tt>normal</tt>, and 
 * <tt>exceptional</tt>.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.19 $
 */

public abstract class JmlGeneralSpecCase extends JmlSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Creates a new <code>JmlGeneralSpecCase</code> instance.
     *
     * @param where a <code>TokenReference</code> value
     * @param specVarDecls an array of spec variable declarations
     *  (<code>JmlSpecVarDecl</code>)
     * @param specHeader an array of requires clauses 
     *  (<code>JmlRequiresClause</code>)
     * @param specBody a specification body (<code>JmlSpecBody</code>)
     */

    //@ requires specHeader != null ==> specHeader.length > 0;
    //@ requires specVarDecls != null ==> specVarDecls.length > 0;
    //@ requires specHeader != null || specBody != null;
    protected JmlGeneralSpecCase(TokenReference where,
				 JmlSpecVarDecl[] specVarDecls,
				 JmlRequiresClause[] specHeader,
				 JmlSpecBody specBody)
    {
	super(where);
	this.specVarDecls = specVarDecls;
	this.specHeader = specHeader;
	this.specBody = specBody;
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
	if( specBody != null ) {
	    assignableFieldSet = specBody.getAssignableFieldSet( method );
	} else {
	    assignableFieldSet = new JmlAssignableFieldSet();
	    if ( !method.isPure() || method.isConstructor() ) {
		assignableFieldSet.setNotSpecified();
	    }
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
	if( specBody != null ) {
	    minAssignableFieldSet 
		= specBody.getMinAssignableFieldSet( method, dataGroupMap );
	} else {
	    minAssignableFieldSet = getAssignableFieldSet( method );
	}
	return minAssignableFieldSet;
    }

    public JmlSpecVarDecl[] specVarDecls() {
	return specVarDecls;
    }

    public JmlRequiresClause[] specHeader() {
	return specHeader;
    }

    public JmlSpecBody specBody() {
	return specBody;
    }

    public boolean hasSpecVarDecls() {
	return specVarDecls != null;
    }

    public boolean hasSpecHeader() {
	return specHeader != null;
    }

    public boolean hasSpecBody() {
	return specBody != null;
    }

    /**
     * Returns true if this general specification case has a non-redunant
     * assignable clause.
     */
    public /*@ pure @*/ boolean hasNonRedundantAssignable() {
        return specBody != null && specBody.hasNonRedundantAssignable();
    }

    /**
     * Returns true if this general specification case has a non-redunant
     * requires clause.
     */
    public /*@ pure @*/ boolean hasNonRedundantRequiresClause() {
        if (specHeader == null)
            return false;
        for (int i = 0; i < specHeader.length; i++) {
            if (!specHeader[i].isRedundantly())
                return true;
        }
        return false;
    }

    /**
     * Returns true if this general specification case has a non-redunant
     * ensures clause.
     */
    public boolean hasNonRedundantEnsures() {
        return specBody != null && specBody.hasNonRedundantEnsures();
    }

    /**
     * Add the given requires clause to this specification case. 
     */
    public void addRequiresClause(/*@ non_null @*/ JmlRequiresClause req) {
        JmlRequiresClause[] reqs = null;
        if (specHeader == null) {
            reqs = new JmlRequiresClause[] { req };
        } else {
            reqs = new JmlRequiresClause[specHeader.length + 1];
            System.arraycopy(specHeader, 0, reqs, 0, specHeader.length);
            reqs[specHeader.length] = req;
        }
        specHeader = reqs;
    }

    //---------------------------------------------------------------------
    // Visitor
    //---------------------------------------------------------------------

	public void accept(/*@ non_null @*/ MjcVisitor m) {
		((JmlVisitor)m).visitJmlGeneralSpecCase(this);
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
     * Typechecks this specification case with the privacy,
     * <code>privacy</code>, in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     * 
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_PROTECTED ||
     *   privacy == ACC_PRIVATE || privacy == 0;
     * </jml></pre>
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context, long privacy,
			   boolean isNestedSpecCase ) 
	throws PositionedError
    {
	// create temp context for storing spec vars
	// newCtx -> newBlock -> orgBody (context) -> ...
	CFlowControlContextType newCtx = context;

	if (specVarDecls != null) {
	    newCtx = context.createFlowControlContext(getTokenReference());

	    for (int i = 0; i < specVarDecls.length; i++) {
		specVarDecls[i].typecheck(newCtx, privacy);
	    }
	}

	if (specHeader != null) {
	    boolean hasSame = false;
	    for (int i = 0; i < specHeader.length; i++) {
		if (specHeader[i] != null) {
		    specHeader[i].typecheck(newCtx, privacy);
		    if (specHeader[i].hasSamePredicate()) {
			if ( hasSame || i > 0 ) {
			    context.reportTrouble(
				new PositionedError( 
				     specHeader[i].getTokenReference(),
				     JmlMessages.DUPLICATE_SAME_PREDICATE )
				);
			}
			if (specBody != null && specBody.isSpecCases()) {
			    context.reportTrouble(
				new PositionedError( 
				     specHeader[i].getTokenReference(),
				     JmlMessages.NESTED_SAME_PREDICATE )
				);
			}
			hasSame = true;
		    }
		}
	    } // end of for loop

	    if ( hasSame && isNestedSpecCase ) {
		context.reportTrouble(
				new PositionedError( 
				     getTokenReference(),
				     JmlMessages.NESTED_SAME_PREDICATE )
				);
	    }
	}

	if (specBody != null) {
	    specBody.typecheck(newCtx, privacy);
	}

	// clean up temp contexts
	if (specVarDecls != null) {
	    newCtx.checkingComplete();
	}
    }

    /**
     * Typechecks this specification case in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError
    {
	// !FIXME! second argument for privacy
        typecheck(context, privacy(context), false);
    }

    
    /** Returns the privacy of this specification case. For a
     * light-weight specification, the default privacy is that of the
     * method; for a heavy-weight specification, it is package
     * visibility.
     *
     * <pre><jml>
     * ensures \result == ACC_PUBLIC || \result == ACC_PROTECTED ||
     *   \result == ACC_PRIVATE || \result == 0;
     * </jml></pre>
     */
    protected long privacy(/*@ non_null @*/ CFlowControlContextType context ) {
        return 0L; // default, i.e., package privacy.
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ invariant specHeader != null || specBody != null;
    //@ invariant specHeader != null ==> specHeader.length > 0;
    //@ invariant specVarDecls != null ==> specVarDecls.length > 0;
    protected JmlSpecVarDecl[] specVarDecls;
    protected JmlRequiresClause[] specHeader;
    protected JmlSpecBody specBody;
    protected JmlAssignableFieldSet assignableFieldSet = null;
    protected JmlAssignableFieldSet minAssignableFieldSet = null;
}
