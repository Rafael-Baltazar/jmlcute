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
 * $Id: JmlAbruptSpecCase.java,v 1.2 2002/03/15 21:43:16 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlAbruptSpecCase.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.2 $
 */

public class JmlAbruptSpecCase extends JmlGeneralSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specHeader != null ==> specHeader.length > 0;
    //@ requires specVarDecls != null ==> specVarDecls.length > 0;
    //@ requires specHeader != null || abruptSpecBody != null;
    public JmlAbruptSpecCase(TokenReference sourceRef,
			      JmlSpecVarDecl[] specVarDecls,
			      JmlRequiresClause[] specHeader,
			      JmlAbruptSpecBody abruptSpecBody) {
	super(sourceRef, specVarDecls, specHeader, abruptSpecBody);
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlAbruptSpecBody abruptSpecBody() {
	return (JmlAbruptSpecBody) specBody;
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

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlAbruptSpecCase(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
}
