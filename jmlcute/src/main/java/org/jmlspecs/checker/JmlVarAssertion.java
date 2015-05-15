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
 * $Id: JmlVarAssertion.java,v 1.5 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents jml-var-assertion in JML ASTs.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public abstract class JmlVarAssertion extends JmlDeclaration {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    public JmlVarAssertion( TokenReference where, long modifiers ) {
	super( where, modifiers, false );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /**
     * Clones this, making a deep copy of any mutable state.
     * Overrides the superclass method, eliminating the
     * <code>CloneNotSupportedException</code>, thus forcing all
     * subclasses to be clonable.  */
    public Object clone() {
	return super.clone();
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    /**
     * Typecheck this variable assertion and mutates the context to
     * store the information obtained during the checking.
     *
     * @param context the context in which this var assertion is declared
     * @exception PositionedError if any checks fail 
     */
    public abstract void typecheck( CContextType context ) 
	throws PositionedError;

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlVarAssertion
