/* $Id: TransExpressionSideEffect.java,v 1.3 2004/08/31 20:51:18 cheon Exp $
 *
 * Copyright (C) 2001-2004 Iowa State University
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
 * A special expression translator that allows translation of
 * expressions with side-effects. Several visitor methods are
 * overridden to translate expressions with side-effects, such as
 * assignment expressions, increment expresions, and decrement
 * expressions.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */
public class TransExpressionSideEffect extends TransExpression {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Constructs an instance and translates the given expression.
	 *
	 * @param varGen variable generator to be used for generating
	 *               fresh variable names necessary in the translated code.
	 * @param ctx context to use for the interpretation of undefinedness.
	 * @param expr expression to be translated.
	 * @param resultVar variable to store the result. In the translated code,
	 *        the result of the expression is stored in the variable whose
	 *        name given by this parameter.
	 * @param typeDecl type declaration from which the expression
	 * <code>expr</code> comes.
	 */
	public TransExpressionSideEffect(
			/*@ non_null @*/ VarGenerator varGen,
			/*@ non_null @*/ RacContext ctx,
			/*@ non_null @*/ JExpression expr,
			/*@ non_null @*/ String resultVar,
			/*@ non_null @*/ JTypeDeclarationType typeDecl) {
		super(varGen, ctx, expr, resultVar, typeDecl);
	}

	/**
	 * Constructs an instance and translates the given expression. If
	 * the expression (or its subexpression) encounters an
	 * undefinedness, no contextual interpretation is done; i.e., the
	 * exception propagates to the caller.
	 *
	 * @param varGen variable generator to be used for generating
	 *               fresh variable names necessary in the translated code.
	 * @param expr expression to be translated.
	 * @param resultVar variable to store the result. In the translated code,
	 *        the result of the expression is stored in the variable whose
	 *        name given by this parameter.
	 * @param typeDecl type declaration from which the expression
	 * <code>expr</code> comes.
	 */
	public TransExpressionSideEffect(
			/*@ non_null @*/ VarGenerator varGen,
			/*@ non_null @*/ JExpression expr,
			/*@ non_null @*/ String resultVar,
			/*@ non_null @*/ JTypeDeclarationType typeDecl) {
		this(varGen, RacContext.createNeutral(), expr, resultVar, typeDecl);
	}

	// ----------------------------------------------------------------------
	// VISITORS FOR TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translates the given assignment expression, <code>self</code>.
	 * The translation rule for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[l = E, r]] = 
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     l = v;
	 * </pre>
	 *
	 * If <code>l</code> is a reference to a model variable, then it
	 * is an error. If <code>l</code> is a reference to a ghost
	 * variable, then the setter method must be used instead of the
	 * assignment (=).
	 */
//	public void visitAssignmentExpression( JAssignmentExpression self ) {
//	transAssignmentExpression(self);
//	}

	/** Translates the given compund assignment expression. */
//	public void visitCompoundAssignmentExpression(
//	JCompoundAssignmentExpression self) {
//	transAssignmentExpression(self);
//	}

	/** Translates the given prefix expression. The translation rule
	 * for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[++E, r]] = 
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     v = v + 1;
	 *     E <- v;
	 *     r = v;
	 * </pre>
	 *
	 * The expression <code>E</code> should be an l-value. If
	 * <code>E</code> is a reference to a ghost variable, its accessor
	 * must be used to get and set its value.
	 */
//	public void visitPrefixExpression( JPrefixExpression self ) {
//	String resultVar = GET_ARGUMENT();
//	JExpression expr = (JExpression) self.expr();
//	CType type = expr.getApparentType();
//	String typeName = TransUtils.toString(type);
//	String initVal = defaultValue(type);

//	// translate the subexpression
//	String var = varGen.freshVar();
//	RacNode eval = translate(expr, var);

//	// compose statements
//	RETURN_RESULT(RacParser.parseStatement(
//	"{\n" + 
//	"  " + typeName + " " + var + " = " + initVal + ";\n" +
//	"$0\n" + 
//	"  " + var + " = " + var + operator(self.oper()) + "1;\n" +
//	"$1\n" + 
//	"  " + resultVar + " = " + var + ";\n" +
//	"}",
//	eval.incrIndent(),
//	assignStmt(expr, var).incrIndent()));
//	}

	/**
	 * Returns the string representation of the desugared increment or
	 * decrement operator.
	 */
//	private static String operator(int opr) {
//		switch (opr) {
//		case OPE_POSTDEC:
//		case OPE_PREDEC:
//			return " - ";
//		case OPE_POSTINC:
//		case OPE_PREINC:
//			return(" + ");
//		}
//
//		//@ unreachable;
//		return null;
//	}

	/** Translates the given prefix expression. The translation rule
	 * for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[E++, r]] = 
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     r = v;
	 *     v = v + 1;
	 *     E <- v;
	 * </pre>
	 *
	 * The expression <code>E</code> should denote an l-value. If
	 * <code>E</code> is a reference to a ghost variable, its accessor
	 * must be used to get and set its value.
	 */
//	public void visitPostfixExpression( JPostfixExpression self ) {
//	String resultVar = GET_ARGUMENT();
//	JExpression expr = (JExpression) self.expr();
//	CType type = expr.getApparentType();
//	String typeName = TransUtils.toString(type);
//	String initVal = defaultValue(type);

//	// translate the subexpression
//	String var = varGen.freshVar();
//	RacNode eval = translate(expr, var);

//	// compose statements
//	RETURN_RESULT(RacParser.parseStatement(
//	"{\n" + 
//	"  " + typeName + " " + var + " = " + initVal + ";\n" +
//	"$0\n" + 
//	"  " + resultVar + " = " + var + ";\n" +
//	"  " + var + " = " + var + operator(self.oper()) + "1;\n" +
//	"$1\n" + 
//	"}",
//	eval.incrIndent(),
//	assignStmt(expr, var).incrIndent()));
//	}

	/** Translates the given assignment expresson. 
	 */
//	public void transAssignmentExpression( JAssignmentExpression expr ) {
//	String resultVar = GET_ARGUMENT();
//	CType type = expr.left().getApparentType();
//	String initVal = defaultValue(type);

//	// translate RHS of the assignment expression
//	String rvar = varGen.freshVar();
//	RacNode rnode = translate(expr.right(), rvar);

//	// compose statements for assigning RHS to LHS
//	JExpression lexpr = (JExpression) expr.left();
//	JStatement result = null;
//	String typeName = TransUtils.toString(type);
//	if (expr instanceof JCompoundAssignmentExpression) {
//	String ivar = varGen.freshVar();
//	result = RacParser.parseStatement(
//	"{\n" + 
//	"  " + typeName + " " + ivar + " = " + initVal + ";\n" +
//	"$0\n" + 
//	"  " + typeName + " " + rvar + " = " + initVal + ";\n" +
//	"$1\n" +
//	"  " + ivar + TransMethodBody.operator(expr) + rvar + ";\n" +
//	"  " + resultVar + " = " + ivar + ";\n" +
//	"$2\n" +
//	"}",
//	translate(lexpr, ivar).incrIndent(),
//	rnode.incrIndent(), 
//	assignStmt(lexpr, ivar).incrIndent());
//	} else {
//	result = RacParser.parseStatement(
//	"{\n" +
//	"  " + typeName + " " + rvar + " = " + initVal + ";\n" +
//	"$0\n" +
//	"  " + resultVar + " = " + rvar + ";\n" +
//	"$1\n" +
//	"}",
//	rnode.incrIndent(),
//	assignStmt(lexpr, rvar).incrIndent());
//	}

//	RETURN_RESULT(result);
//	}

	/** Generates a statement that assigns the value of var to expr. */
//	private RacNode assignStmt(JExpression expr, String var) { 
//	if (JmlSetStatement.isGhostFieldReference(expr)) {
//	TransMethodBody.getGhostFieldSetter(
//	(JClassFieldExpression) expr, var, varGen);
//	}
//	if (expr instanceof JClassFieldExpression) {
//	String ident = ((JClassFieldExpression) expr).ident();
//	int index = ident.indexOf("_$");
//	if (index != -1) { // local variable?
//	return RacParser.parseStatement(
//	ident.substring(0, index) + " = " + var +";");
//	}
//	}
//	return RacParser.parseStatement(
//	"$0 = " + var + ";", 
//	expr);
//	}
}
