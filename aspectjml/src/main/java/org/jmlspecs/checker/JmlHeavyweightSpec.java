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
 * $Id: JmlHeavyweightSpec.java,v 1.9 2006/09/13 17:42:02 ye-cui Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.*;

/**
 * An AST node class for the JML <tt>heavyweight-spec</tt>. The production
 * rule <tt>heavyweight-spec</tt> is defined as follows.
 *
 * <pre>
 *  heavyweight-spec ::= [ privacy ] [code] "behavior" generic-spec-case
 *    | [ privacy ] [code] "exceptional_behavior" exceptional-spec-case
 *    | [ privacy ] [code] "normal_behavior" normal-spec-case
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public abstract class JmlHeavyweightSpec extends JmlSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /*@
      @ requires privacy == 0 ||
      @    privacy == Constants.ACC_PUBLIC ||
      @    privacy == Constants.ACC_PROTECTED ||
      @    privacy == Constants.ACC_PRIVATE;
      @*/
    public JmlHeavyweightSpec( TokenReference where, long privacy,
			    /*@ non_null */ JmlGeneralSpecCase specCase )
    {
	super( where );
	this.specCase = specCase;
	this.privacy = privacy;
	if (hasFlag(privacy, Constants.ACC_CODE)) {
	    this.privacy ^= Constants.ACC_CODE; // remove the code modifier
	    this.isCodeSpec = true;
	} else {
	    this.isCodeSpec = false;
	}
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public long privacy() {
	return privacy;
    }

    //@ ensures \result != null;
    public JmlGeneralSpecCase specCase() {
	return specCase;
    }

    public boolean isCodeSpec() {
	return isCodeSpec;
    }

    public boolean isNestedSpec() {
	return specCase.hasSpecBody() && specCase.specBody().isSpecCases();
    }

    /**
     * Returns the maximal set of fields that can be assigned to by 
     * the given method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public JmlAssignableFieldSet getAssignableFieldSet( JmlSourceMethod method )
    {
	return specCase.getAssignableFieldSet( method );
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
     * Typechecks this <tt>heavyweight-spec</tt> in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    /*@ requires context.getCMethod() != null; */
    public void typecheck( /*@non_null@*/ CFlowControlContextType context ) 
	throws PositionedError
    {
        // The access modifier of a heavyweight specification case
        // cannot allow more access than the method being specified
        // [JML 7.3].
        long mod = context.getCMethod().modifiers();
        boolean ok = false;
	if (privacy == ACC_PUBLIC) {
            ok = hasFlag(mod, ACC_PUBLIC | ACC_SPEC_PUBLIC);
	} else if(privacy == ACC_PROTECTED) {
            ok = hasFlag(mod, ACC_PUBLIC | ACC_SPEC_PUBLIC |
                         ACC_PROTECTED | ACC_SPEC_PROTECTED);
	} else if(privacy == 0) { // default, i.e., package 
           ok = !hasFlag(mod, ACC_PRIVATE) || 
                   hasFlag(mod, ACC_SPEC_PUBLIC | ACC_SPEC_PROTECTED);
	} else if(privacy == ACC_PRIVATE) {
            ok = true;
	}

	check(context, ok, JmlMessages.METHOD_SPEC_PRIVACY);

        // check if this behavior specification has an assigable clause
        if (Main.jmlOptions.assignable() && !isCurrentMethodPure(context)) {
	    boolean noAssignableWarning 
		= specCase.hasNonRedundantAssignable();
	    if ( !noAssignableWarning && isCodeSpec() 
		 && specCase.hasSpecHeader() ) {

		JmlRequiresClause req[] = specCase.specHeader();
		if ( req[0].predOrNot() != null 
		     && req[0].predOrNot().isSameKeyword() ) {
		    // do not emit warning if spec is a code contract 
		    // with requires \same and no ensures clause.

		    noAssignableWarning = !specCase.hasNonRedundantEnsures();
		}
	    }
	    warnAssignable(noAssignableWarning, context);
        }
        
        // check the specification case
	specCase.typecheck(context, privacy, false);
	// the third parameter above says that this specCase is not nested 
	// inside another spec case; it can't be since this is the top level
	// of a heavyweight specification case.
    }

    /**
     * Produce a caution message about missing assignable clause.
     */
    private void warnAssignable(boolean condition, CContextType context) {
        if (!condition) {
            context.reportTrouble(new CWarning(getTokenReference(),
                                               JmlMessages.NO_ASSIGNABLE));
        }
    }
    
    /**
     * Returns true if the current method being type checked has a
     * pure annotation.
     */
    private boolean isCurrentMethodPure(CFlowControlContextType context) {
        CMethod meth = context.getCMethod();
	//@ assert meth instanceof JmlSourceMethod;
	return ((JmlSourceMethod) meth).isPure();      
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public abstract void accept( /*@non_null@*/ MjcVisitor p );

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ private invariant privacy == 0 ||
      @    privacy == Constants.ACC_PUBLIC ||
      @    privacy == Constants.ACC_PROTECTED ||
      @    privacy == Constants.ACC_PRIVATE;
      @*/
    private long privacy;

    private boolean isCodeSpec;

    private /*@ non_null */ JmlGeneralSpecCase specCase;

} // JmlHeavyweightSpec
