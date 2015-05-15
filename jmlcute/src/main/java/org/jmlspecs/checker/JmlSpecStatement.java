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
 * $Id: JmlSpecStatement.java,v 1.12 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlSpecStatement.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.12 $
 */

public class JmlSpecStatement extends JmlModelProgStatement {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Construct a JMLSpecStatement.
     * <pre><jml>
     * requires specCase != null;
     * </jml></pre>
     */
    public JmlSpecStatement(/*@ non_null */ TokenReference where,
    		/*@ non_null */ JmlGeneralSpecCase specCase,
    		/*@ nullable */ JavaStyleComment[] comments ) {
	super( where, comments );
	this.specCase = specCase;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------
    
    public /*@non_null@*/ JmlGeneralSpecCase specCase() {
	return specCase;
    }

    public boolean isGeneric() {
	return specCase instanceof JmlGenericSpecCase;
    }

    public boolean isExceptional() {
	return specCase instanceof JmlExceptionalSpecCase;
    }

    public boolean isNormal() {
	return specCase instanceof JmlNormalSpecCase;
    }

    public boolean isAbrupt() {
	return specCase instanceof JmlAbruptSpecCase;
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
    public void typecheck( /*@non_null@*/  CFlowControlContextType context )
	throws PositionedError 
    {
	// !FIXME! second argument for privacy
	this.typecheck( context, 0 );
    }

    public void typecheck( /*@non_null@*/ CFlowControlContextType context, long privacy )
	throws PositionedError 
    {
	// the third parameter says that this is not a nested spec case
	specCase.typecheck( context, privacy, false );
    }

    /** Returns an appropriate context for checking this clause. */
    protected /*@non_null@*/ JmlExpressionContext 
	createContext( /*@non_null@*/ CFlowControlContextType context ) {
        return JmlExpressionContext.createPrecondition( context );
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlSpecStatement(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@non_null@*/ JmlGeneralSpecCase specCase;

}
