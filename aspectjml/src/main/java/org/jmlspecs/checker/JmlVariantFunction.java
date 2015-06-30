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
 * $Id: JmlVariantFunction.java,v 1.4 2004/06/28 14:30:00 wdietl Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.MjcVisitor;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * JmlVariantFunction.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.4 $
 */

public class JmlVariantFunction extends JmlLoopSpecification {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlVariantFunction(TokenReference where, boolean isRedundantly,
			      JmlSpecExpression specExpression) 
    {
	super( where, isRedundantly );
	this.specExpression = specExpression;
        this.isInformal = false;

        //@ assume specExpression != null;

        // make an int-typed informal description out of boolean-typed one
        if (specExpression.expression() instanceof JmlInformalExpression) {
            this.specExpression = new JmlSpecExpression(
                JmlInformalExpression.ofInteger(
                    (JmlInformalExpression) specExpression.expression()));
            isInformal = true;
        }
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ JmlSpecExpression specExpression() {
	return specExpression;
    }

    /** Returns true if this variant function is of informal
     * description. */
    public /*@ pure @*/ boolean isInformal() {
	return isInformal;
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

    public void typecheck( CExpressionContextType context )
	throws PositionedError 
    {
        try {
            enterSpecScope();

            //@ assert specExpression != null;
            specExpression = (JmlSpecExpression)specExpression.typecheck(
                context );
            check(context, 
                  specExpression.getType().isOrdinal(),
                  JmlMessages.BAD_TYPE_IN_DECREASING_STATEMENT, 
                  specExpression.getType().toVerboseString() );
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
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlVariantFunction(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JmlSpecExpression specExpression;

    /** Indicates whether this is an informal description or not. */
    private boolean isInformal;
}
