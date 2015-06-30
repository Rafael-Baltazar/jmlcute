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
 * $Id: JmlStoreRefKeyword.java,v 1.11 2005/09/07 19:42:14 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a JmlStoreRefKeyword in the AST.
 *
 * <pre>
 *  store-ref-keyword ::= "\nothing" | "\everything" | "\not_specified" 
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.11 $
 */
public class JmlStoreRefKeyword extends JmlStoreRef implements Constants 
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    /*@ requires code == NOTHING || code == EVERYTHING || 
      @          code == NOT_SPECIFIED;
      @*/
    public JmlStoreRefKeyword( TokenReference where, int code ) {
	super( where );
	this.code = code;
    }
    
    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isNothing() {
	return code == NOTHING;
    }

    public /*@ pure @*/ boolean isEverything() {
	return code == EVERYTHING;
    }

    public boolean isNotSpecified() {
	return code == NOT_SPECIFIED;
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    //@ also
    //@ ensures (* returns true iff this does not reference non-local variables *);
    public /*@ pure @*/ boolean isLocalVarReference() {
	return isNothing();
    }

    /**
     * Typechecks this store reference in the given visibility,
     * <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @return a desugared store reference
     * @exception PositionedError if the check fails */
    public JmlStoreRef typecheck( CExpressionContextType context,
                                  long privacy )
	throws PositionedError 
    {
	// nothing to type check
	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlStoreRefKeyword(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private final int code;

    // -------------------------------------------------------------
    // STATIC UTILITIES
    // -------------------------------------------------------------

}// JmlStoreRefKeyword
