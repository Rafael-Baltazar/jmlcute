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
 * $Id: JmlStoreRefListWrapper.java,v 1.2 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlStoreRefListWrapper.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.2 $
 */

public abstract class JmlStoreRefListWrapper extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlStoreRefListWrapper( /*@non_null*/TokenReference where,
    		/*@non_null*/JmlStoreRef[] storeRefList ) {
	super( where );
	this.storeRefList = storeRefList;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlStoreRef[] storeRefList() {
	return storeRefList;
    }

    public /*@non_null@*/ CType getType() {
	return CStdType.Boolean;
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
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return a desugared Java expression
     * @exception PositionedError if the check fails */
    public /*@non_null@*/ JExpression 
	typecheck(/*@non_null@*/  CExpressionContextType context ) 
	throws PositionedError 
    {
	if (!(context instanceof JmlExpressionContext)) {
	    throw new IllegalArgumentException(
	      "JmlExpressionContext object expected");
	}

	for (int i = 0; i < storeRefList.length; i++) {
	    //@ assert storeRefList[i] != null;
	    storeRefList[i] = storeRefList[i].typecheck(context, ACC_PRIVATE);
	}
	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant \nonnullelements(storeRefList);
    private /*@non_null*/JmlStoreRef[] storeRefList;

}// JmlStoreRefListWrapper
