/*
 * Copyright (C) 2006 DSRG, Concordia University
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
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlArrayDimsAndInits.java
 *
 * @author Perry James
 */

public class JmlArrayDimsAndInits extends JArrayDimsAndInits 
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Constructs an array dimension and initializer node in the AST
     * @param	where	a reference to the source file generating this node
     * @param   array_univ      the universe of the whole array WMD
     *                  Maybe better in JNewArrayExpression.
     * @param	dims	an array of the dimension expression AST nodes
     * @param	init	an initializer AST node
     * @param	mods	a modifier bit-mask
     */ 
    public JmlArrayDimsAndInits(TokenReference where, 
			      CUniverse array_univ, // WMD
			      JExpression[] dims, 
			      JArrayInitializer init,
			      long mods) {
	super(where, array_univ, dims, init);
	this.mods = mods;
    }
	    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /**
     * Returns true iff the value represented by this expression is non-null
     */
    public /*@pure*/ boolean isNonNull(/*@non_null@*/ CContextType context) {
	    if (mods == 0)
	       return super.isNonNull(context);
	    else
	       return hasFlag(mods, ACC_NON_NULL | IMPLICITLY_NON_NULL);
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
     * Typechecks this array dimension and initialization instruction
     * in the given context.
     * @param	context		the context in which this instruction appears
     * @param	type		type of the array which we are creating, 
     *				ignored if this is part of an array dimension 
     *				statement like <code>new Integer[1][2][3], 
     *				used if this is part of an array 
     *				initialization like <code>Integer[] foo = 
     *				{ 1, 2, 3 }</code>
     * @return	the type of the array that is being created
     * @exception PositionedError if a check fails */
    public CType typecheck(CExpressionContextType context, CType type) 
	throws PositionedError {
	if (mods != 0) {
		check( context, 
		       !this.isNonNull(context) || super.isNonNull(context),
		       JmlMessages.ARRAY_NULLITY_DECLARATION_MISMATCH);
	}
	return super.typecheck(context, type);
    }


    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private long mods;
}
