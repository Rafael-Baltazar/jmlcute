/*
 * Copyright (C) 2003 Iowa State University.
 *
 * This file is part of jml, the Java Modeling Language Checker.
 *
 * based in part on work:
 *
 * Copyright (C) 2000-2001 Iowa State University
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
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
 * $Id: JmlExpressionFactory.java,v 1.5 2006/12/11 05:59:03 chalin Exp $
 */

package org.jmlspecs.checker;

import antlr.*;
import org.multijava.mjc.*;
import org.multijava.util.compiler.*;

/**
 * Expression AST node factory class.  Factory methods are provided for
 * expressions whose semantics are different in Java and JML annotations.
 */
public class JmlExpressionFactory extends JExpressionFactory {

    /* General method property: the Token passed as first argument is the
     * token of the expression operator. This token occurs within an
     * annotation of it is an instanceof CToken, otherwise it will simply be
     * an instanceof Token.
     */

    public /*@ non_null @*/ JUnaryExpression 
	createUnaryExpression(/*@ non_null @*/ Token op, 
			      /*@ non_null @*/ TokenReference where, 
			      int oper, 
			      /*@ non_null @*/ JExpression expr) {
        return (op instanceof CToken)
	    ? new JmlUnaryExpression(where, oper, expr)
            : new JUnaryExpression(where, oper, expr);
    }

    public /*@ non_null @*/ JAddExpression 
	createAddExpression(/*@ non_null @*/ Token tok, 
			    /*@ non_null @*/ TokenReference where, 
			    /*@ non_null @*/ JExpression left, 
			    /*@ non_null @*/ JExpression right) {
        return (tok instanceof CToken)
            ? new JmlAddExpression(where, left, right)
            : new JAddExpression(where, left, right);
    }
   
    public /*@ non_null @*/ JMinusExpression 
	createMinusExpression(/*@ non_null @*/ Token tok, 
			      /*@ non_null @*/ TokenReference where, 
			      /*@ non_null @*/ JExpression left, 
			      /*@ non_null @*/ JExpression right) {
        return (tok instanceof CToken)
            ? new JmlMinusExpression(where, left, right)
            : new JMinusExpression(where, left, right);
    }
    
    public /*@ non_null @*/ JMultExpression 
	createMultExpression(/*@ non_null @*/ Token op, 
			     /*@ non_null @*/ TokenReference where, 
			     /*@ non_null @*/ JExpression left, 
			     /*@ non_null @*/ JExpression right) {
        return (op instanceof CToken)
            ? new JmlMultExpression(where, left, right)
            : new JMultExpression(where, left, right);
    }
    
    public /*@ non_null @*/ JDivideExpression 
	createDivideExpression(/*@ non_null @*/ Token op, 
			       /*@ non_null @*/ TokenReference where, 
			       /*@ non_null @*/ JExpression left, 
			       /*@ non_null @*/ JExpression right) {
        return (op instanceof CToken)
            ? new JmlDivideExpression(where, left, right)
            : new JDivideExpression(where, left, right);
    }
}
