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
 * $Id: JmlLoopInvariant.java,v 1.5 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlLoopInvariant.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlLoopInvariant extends JmlLoopSpecification {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlLoopInvariant( /*@ non_null */ TokenReference where, boolean isRedundantly,
			     /*@non_null@*/ JmlPredicate predicate ) 
    {
	super( where, isRedundantly );
	this.predicate = predicate;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@non_null@*/ JmlPredicate predicate() {
	return predicate;
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

    public void typecheck( /*@non_null@*/ CExpressionContextType context ) 
	throws PositionedError 
    {
        try {
            enterSpecScope();
            predicate = (JmlPredicate) predicate.typecheck( context );
        }
        finally {
            exitSpecScope();
        }
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
	    ((JmlVisitor)p).visitJmlLoopInvariant(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@non_null@*/ JmlPredicate predicate;
}
