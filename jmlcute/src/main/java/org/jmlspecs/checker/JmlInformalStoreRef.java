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
 * $Id: JmlInformalStoreRef.java,v 1.5 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlInformalStoreRef.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlInformalStoreRef extends JmlStoreRef {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlInformalStoreRef( TokenReference where, String text ) {
	super( where );
	this.text = text;
    }
    

    // -------------------------------------------------------------
    // ACCESSORS
    // -------------------------------------------------------------

    public String text() {
	return text;
    }

    public boolean isInformalStoreRef() {
	return true;
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
     * Typechecks this store reference in the given visibility,
     * <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @return a desugared store reference
     * @exception PositionedError if the check fails */
    public JmlStoreRef typecheck(CExpressionContextType context, long privacy) 
	throws PositionedError 
    {
	// nothing to type check for informal store ref.
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
	    ((JmlVisitor)p).visitJmlInformalStoreRef(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * The text of this informal description store reference.  */
    private final String text;

}// JmlInformalStoreRef
