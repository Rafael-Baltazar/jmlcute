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
 * $Id: JmlInterfaceContext.java,v 1.4 2003/08/13 00:57:06 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents the context for an interface declaration
 * during checking passes (checkInterface, checkInitializers,
 * typecheck).
 * @see CContextType 
 */
public class JmlInterfaceContext extends JmlClassContext 
    implements CInterfaceContextType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Instantiates a context for checking interface declarations.
     * Clients should not call this but should instead call
     * <code>CContextType.createInterfaceContext</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * </jml></pre>
     * @param	parent		the parent context or null at top level
     * @param	clazz		the corresponding clazz
     *
     * @see CContextType#createInterfaceContext(CClass)
     */
    JmlInterfaceContext(CContextType parent, CClass clazz) {
	super(parent);
	delegee = new CInterfaceContext(parent, clazz);
    }

    /**
     * Verifies all final fields are initialized.
     * !FIXME! Currently
     * checks nothing.  Probably needs to check that fields are
     * initialized since interfaces can have fields (or does this
     * initialization then fall to implementors?).
     * @exception UnpositionedError if any checks fail
     */
    public void checkingComplete(JTypeDeclarationType decl,
				  CVariableInfoTable staticC,
				  CVariableInfoTable instanceC,
				  CVariableInfoTable[] constructorsC)
	throws UnpositionedError 
    {
	if (! Main.isSpecOrJmlMode(decl.getTokenReference())) {
	    ((CInterfaceContext)delegee).checkingComplete(decl, 
							  staticC, 
							  instanceC,
							  constructorsC);
	}
    }

}

