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
 * $Id: JmlWritableIfVarAssertion.java,v 1.2 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * This class represents a jml-var-assertion of the form 
 * <code>writable</code> <em>id</em> <code>if</code> <em>predicate</em>.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.2 $
 */
public class JmlWritableIfVarAssertion extends JmlVarAssertion {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlWritableIfVarAssertion( TokenReference where, long modifiers, 
				      JNameExpression fieldName,
				      JmlPredicate predicate ) {
	super( where, modifiers );
	this.fieldName = fieldName;
	this.predicate = predicate;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public Object clone() {
	return super.clone();
    }

    public String fieldIdent() {
	return fieldName.getName();
    }

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
     * Typecheck this variable assertion and mutates the context to
     * store the information obtained during the checking.
     *
     * @param context the context in which this var assertion is declared
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CContextType context ) 
	throws PositionedError 
    {
	try {
	    enterSpecScope();

            // check modifiers
            checkModifiers(context);

	    JmlExpressionContext ectx = createContext(context);
	    fieldExpr = fieldName.typecheck(ectx);

            // purity and visibility check
	    long privacy = privacy();
            JmlExpressionChecker.perform(ectx, privacy, fieldExpr);

            // check the predicate part
	    predicate.typecheck( ectx, privacy );
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
	    ((JmlVisitor)p).visitJmlWritableIfVarAssertion(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@ non_null @*/ JExpression fieldExpr = null;
    private /*@ non_null @*/ JNameExpression fieldName = null;
    private /*@ non_null @*/ JmlPredicate predicate;

}// JmlWritableIfVarAssertion
