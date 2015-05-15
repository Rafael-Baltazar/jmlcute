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
 * $Id: JmlInvariant.java,v 1.13 2005/12/22 20:50:50 darvasa Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CContextType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This AST node represents a JML invariant annotation.
 * The syntax for the invariant annotation is as follows.
 *
 * <pre>
 *  invariant ::= invariant-keyword predicate ";"
 *  invariant-keyword ::= "invariant" | "invariant_redundantly"
 * </pre>
 */
public class JmlInvariant extends JmlDeclaration implements Cloneable {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /**
     * Construct an invariant annotation AST.  */
    public JmlInvariant( TokenReference where, long modifiers, 
			 boolean redundantly, JmlPredicate predicate ) {
	super( where, modifiers, redundantly );
	this.predicate = predicate;
    }

    public Object clone() {
	return super.clone();
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public JmlPredicate predicate() {
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

    /**
     * Typechecks this invariant clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CContextType context ) throws PositionedError 
    {

	try {
 	    enterSpecScope();
// 	    if (Main.jmlOptions.nonnull()){
// 	    	String fn=Utils.getFilePath(getTokenReference().file());
// 	    	if (isStatic())
// 	    		NonNullStatistics.checkExpression(predicate().specExpression().expression(), (JmlContext)context, fn,2,false, true);
// 	    	else
// 	    		NonNullStatistics.checkExpression(predicate().specExpression().expression(), (JmlContext)context, fn,2,false, false);
// 	    }
	    
            checkModifiers(context);
	    JmlExpressionContext ectx = createContext(context);
	    predicate = (JmlPredicate) predicate.typecheck( ectx, privacy() );
		/* rzakhejm begin */
	    /* Admissibility check */
		if (JmlAdmissibilityVisitor.isAdmissibilityCheckEnabled()) {
			if (!isStatic())
				JmlAdmissibilityVisitor.checkInvariant(this, ectx);
			else
				warn(context, JmlMessages.ADMISSIBILITY_STATICS_NOT_SUPPORTED, predicate);
		}
		/* rzakhejm end */
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
	    ((JmlVisitor)p).visitJmlInvariant(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * An AST for the predicate clause of this invariant.  */
    private /*@ non_null @*/ JmlPredicate predicate;

}
