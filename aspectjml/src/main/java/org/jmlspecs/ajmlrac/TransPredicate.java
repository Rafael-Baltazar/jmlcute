/* $Id: TransPredicate.java,v 1.9 2003/01/26 19:46:21 davidcok Exp $
 *
 * Copyright (C) 2001 Iowa State University
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
 */

package org.jmlspecs.ajmlrac;

import org.multijava.mjc.JExpression;
import org.multijava.mjc.JTypeDeclarationType;

/**
 * A RAC visitor class for transforming JML predicates into Java code.
 * The generated code is a sequence of Java statements that evaluate 
 * and store the boolean result in the given variable. The boolean
 * result variable is assumed to be declared in the outer scope that
 * incorporates the code. 
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 * @see TransExpression
 */
public class TransPredicate extends TransExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new instance.
     *
     * @param varGen variable generator for generating fresh local variables
     * @param pred taget predicate to translate
     * @param resultVar variable name to store the result
     */
     public TransPredicate( /*@ non_null @*/ VarGenerator varGen,
                            /*@ non_null @*/ RacContext ctx,
			    /*@ non_null @*/ JExpression pred,
			    /*@ non_null @*/ String resultVar,
			    /*@ non_null @*/ JTypeDeclarationType typeDecl) {
	 super(varGen, ctx, pred, resultVar, typeDecl);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /** Returns the result of translating the expression wrapped in a
     * try-catch statement to assign the given default values if an
     * exception or non-executability happens while evaluating the
     * expression. The returned code has the following structure.
     *
     * <pre>
     * try {
     *  [[E, r]]
     * } catch (JMLNonExecutableException e) {
     *  r = ctx;
     * } catch (Exception e) {
     *  r = !ctx;
     * }
     * </pre>
     *
     * where <code>E</code> is the target expression to translate and
     * <code>r</code> is the variable to hold the result of the
     * expression. The value assinged to <code>r</code> is
     * context-sensitive, i.e., it is true in a positive context and
     * false in a negative context.
     *
     * @see #stmt()
     */
    public /*@ non_null @*/ RacNode wrappedStmt() {
        perform();
	return RacParser.parseStatement(
	  "try {\n" +
	    "$0\n" +
	  "}\n" +
	  "catch (JMLNonExecutableException jml$e0) {\n" +
	  "  " + context.angelicValue(resultVar) + ";\n" + 
	  "}\n" +
	  "catch (java.lang.Exception jml$e0) {\n" +
	  "  " + context.demonicValue(resultVar) + ";\n" + 
	  "}", 
	  ((RacNode)resultStack.peek()).incrIndent());
    }
}

