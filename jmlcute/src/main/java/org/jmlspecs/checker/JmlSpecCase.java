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
 * $Id: JmlSpecCase.java,v 1.8 2006/09/13 17:42:02 ye-cui Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * An abstraction of JML specification cases. JML supports three kinds of
 * specification cases (<tt>spec-case</tt>) and this class is the common
 * superclass. In JML, the production rule <tt>spec-case</tt> is defined 
 * as follows.
 *
 * <pre>
 *  spec-case :: = generic-spec-case | behavior-spec | model-program
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.8 $
 */

public abstract class JmlSpecCase extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    protected JmlSpecCase( TokenReference where ) {
	super( where );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

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
     * this method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public abstract JmlAssignableFieldSet getAssignableFieldSet(
					       JmlSourceMethod method );

    /**
     * Typechecks this specification case in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public abstract void typecheck( CFlowControlContextType context ) 
	throws PositionedError;

    public boolean isCodeSpec() {
	return false;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlSpecCase
