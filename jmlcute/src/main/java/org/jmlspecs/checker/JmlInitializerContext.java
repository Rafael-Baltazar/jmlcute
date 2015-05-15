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
 * $Id: JmlInitializerContext.java,v 1.2 2002/03/15 21:43:17 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CInitializerContext;
import org.multijava.mjc.CInitializerContextType;
import org.multijava.mjc.CMethod;

/**
 * This class represents the context for a static initializer during checking
 * passes (checkInterface, checkInitializers, typecheck).
 * @see CContextType 
 */
public class JmlInitializerContext extends JmlMethodContext 
    implements CInitializerContextType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Instantiates a context for checking initializer declarations.
     * Clients should not call this but should instead call
     * <code>CClassContextType.createInitializerContext</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * </jml></pre>
     *
     * @param	parent		the parent context
     * @param	self		the corresponding method interface
     *
     * @see CClassContextType#createInitializerContext(CMethod)
     */
    public JmlInitializerContext(CContextType parent, CMethod self) {
	super(parent);
	delegee = new CInitializerContext(parent, self);
    }

    // -------------------------------------------------------------
    // ACCESSORS
    // -------------------------------------------------------------

    /**
     * Indicates whether this context is enclosed in an instance or
     * static initializer.  */
    public boolean isInInitializer() {
	return ((CInitializerContext)delegee).isInInitializer();
    }
}
