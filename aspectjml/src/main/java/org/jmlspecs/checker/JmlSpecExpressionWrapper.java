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
 * $Id: JmlSpecExpressionWrapper.java,v 1.5 2006/12/20 06:16:02 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.util.compiler.TokenReference;

/**
 * This abstract class is the super class of all JmlExpressions that
 * simply modify a spec-expression (e.g. <code>\old</code> and
 * <code>\nonnullelements</code>)
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $ */

public abstract class JmlSpecExpressionWrapper extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlSpecExpressionWrapper( /*@ non_null */ TokenReference where, 
    		/*@ non_null @*/JmlSpecExpression specExpression ) {
	super( where );
	this.specExpression = specExpression;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ /*@ non_null @*/ JmlSpecExpression specExpression() {
	return specExpression;
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

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    protected /*@ non_null */ JmlSpecExpression specExpression;

}// JmlSpecExpressionWrapper
