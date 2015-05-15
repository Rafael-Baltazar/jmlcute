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
 * $Id: JmlQuotedExpressionWrapper.java,v 1.1 2003/03/03 15:40:48 leavens Exp $
 */

package org.jmlspecs.checker;
import org.multijava.util.compiler.TokenReference;
import org.multijava.mjc.JExpression;

/**
 * This abstract class is the super class of all JmlExpressions that
 * simply modify a quoted Java expression (e.g. <code>\space</code> and
 * <code>\duration</code>)
 *
 * @author Gary T. Leavens
 * @version $Revision: 1.1 $ */

public abstract class JmlQuotedExpressionWrapper extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlQuotedExpressionWrapper( TokenReference where, 
				     JExpression expression ) {
	super( where );
	this.expression = expression;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ JExpression expression() {
	return expression;
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

    protected JExpression expression;

}// JmlQuotedExpressionWrapper
