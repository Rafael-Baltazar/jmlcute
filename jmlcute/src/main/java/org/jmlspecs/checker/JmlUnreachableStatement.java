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
 * $Id: JmlUnreachableStatement.java,v 1.2 2002/03/15 21:43:17 cclifton Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;

/**
 * JmlUnreachableStatement.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.2 $
 */

public class JmlUnreachableStatement extends JStatement {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlUnreachableStatement( TokenReference where,
				    JavaStyleComment[] comments ) {
	super( where, comments );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** 
     * Returns the Java source code generated by jmlrac to check 
     * this assertion at runtime. */
    public JStatement assertionCode() {
	return assertionCode;
    }

    /** 
     * Returns <code>true</code> if this assertion has the Java source 
     * code generated by jmlrac to check the assertion at runtime. */
    public boolean hasAssertionCode() {
	return assertionCode != null;
    }

    /** 
     * Sets the Java source code generated by jmlrac to check 
     * this assertion at runtime. */
    public void setAssertionCode(JStatement code) {
	assertionCode = code;
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

    public void typecheck( CFlowControlContextType context ) throws PositionedError {
	// nothing to typecheck :-)
//      no support in AspectJML --- [[[hemr]]]
        check(context, 
                false,
                JmlMessages.NO_SUPPORT_UNREACHABLE_STATEMENT);
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    public void genCode( CodeSequence code ) {
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlUnreachableStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /** Java source code generated by jmlrac to check the assertion
     * at runtime. */
    private JStatement assertionCode;
}
