/*
 * Copyright (C) 2001, 2002 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: TransOldExpression.java,v 1.6 2005/08/23 06:13:19 cruby Exp $
 */

package org.jmlspecs.ajmlrac;

import org.multijava.mjc.*;

/**
 * A RAC visitor class for transforming JML old expressions into Java code.
 * The generated code is a sequence of Java statements that evaluate 
 * and store the result in the given variable. The result variable is 
 * assumed to be declared in the outer scope that incorporates the code.
 * See <code>TransExpression</code> for more explanation.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.6 $
 */
public class TransOldExpression extends TransExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct an object of <code>TransOldExpression</code>.
     *
     * @param varGen variable generator for generating fresh local variables
     * @param expr target predicate to translate
     * @param resultVar variable name to store the result
     */
     public TransOldExpression( /*@ non_null @*/ VarGenerator varGen,
                                /*@ non_null @*/ RacContext ctx,
				/*@ non_null @*/ JExpression expr,
				/*@ non_null @*/ String resultVar,
				/*@ non_null @*/ JTypeDeclarationType typeDecl) {
	 super(varGen, ctx, expr, resultVar, typeDecl);
    }
}

