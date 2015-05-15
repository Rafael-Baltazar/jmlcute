/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
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
 * $Id: JmlConstructorContext.java,v 1.2 2002/03/15 21:43:16 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents the context for a constructor during checking
 * passes (checkInterface, checkInitializers, typecheck).  It includes
 * data on whether the constructor calls a super constructor.
 * @see CContextType 
 */
public class JmlConstructorContext extends JmlMethodContext 
    implements CConstructorContextType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * CConstructorContext
     * Clients should not call this but should instead call
     * <code>CClassContextType.createConstructorContext</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * </jml></pre>
     *
     * @param	parent		the parent context
     * @param	self		the corresponding method interface
     *
     * @see CClassContextType#createConstructorContext(CMethod)
     */
    JmlConstructorContext(CContextType parent, CMethod self) {
	super(parent);
	delegee = new CConstructorContext(parent, self);
    }

    /**
     * Verifies that all checked exceptions are defined in the throw
     * list.  Sets the throwables of the constructor if it is the
     * synthetic constructor of an anonymous class.
     *
     * @exception PositionedError if checks fail */
    public void verifyExceptions(TokenReference ref) throws PositionedError {
	((CConstructorContext)delegee).verifyExceptions(ref);
    }

    // -------------------------------------------------------------
    // ACCESSORS
    // -------------------------------------------------------------

    /**
     * Indicates whether this context is enclosed in a constructor.  */
    public boolean isInConstructor() {
	return ((CConstructorContext)delegee).isInConstructor();
    }
    
    /**
     *
     */
    public void setSuperConstructorCalled(boolean b) {
	((CConstructorContext)delegee).setSuperConstructorCalled(b);
    }

    /**
     *
     */
    public boolean isSuperConstructorCalled() {
	return ((CConstructorContext)delegee).isSuperConstructorCalled();
    }
    
    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------
}
