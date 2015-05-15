/* $Id: TransExpression.java,v 1.104 2007/02/03 02:04:50 delara Exp $
 *
 * Copyright (C) 2001-2005 Iowa State University
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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import org.jmlspecs.ajmlrac.qexpr.TransQuantifiedExpression;
import org.jmlspecs.checker.JmlElemTypeExpression;
import org.jmlspecs.checker.JmlFreshExpression;
import org.jmlspecs.checker.JmlInformalExpression;
import org.jmlspecs.checker.JmlIsInitializedExpression;
import org.jmlspecs.checker.JmlLabelExpression;
import org.jmlspecs.checker.JmlLockSetExpression;
import org.jmlspecs.checker.JmlMaxExpression;
import org.jmlspecs.checker.JmlNonNullElementsExpression;
import org.jmlspecs.checker.JmlNotAssignedExpression;
import org.jmlspecs.checker.JmlNotModifiedExpression;
import org.jmlspecs.checker.JmlOldExpression;
import org.jmlspecs.checker.JmlPreExpression;
import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlReachExpression;
import org.jmlspecs.checker.JmlRelationalExpression;
import org.jmlspecs.checker.JmlResultExpression;
import org.jmlspecs.checker.JmlSetComprehension;
import org.jmlspecs.checker.JmlSourceClass;
import org.jmlspecs.checker.JmlSourceField;
import org.jmlspecs.checker.JmlSourceMethod;
import org.jmlspecs.checker.JmlSpecExpression;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.jmlspecs.checker.JmlStdType;
import org.jmlspecs.checker.JmlTypeExpression;
import org.jmlspecs.checker.JmlTypeOfExpression;
import org.jmlspecs.checker.JmlVariableDefinition;
import org.multijava.mjc.CArrayType;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CField;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CNumericType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JAddExpression;
import org.multijava.mjc.JArrayAccessExpression;
import org.multijava.mjc.JArrayDimsAndInits;
import org.multijava.mjc.JArrayInitializer;
import org.multijava.mjc.JArrayLengthExpression;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JBinaryExpression;
import org.multijava.mjc.JBitwiseExpression;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JCharLiteral;
import org.multijava.mjc.JClassExpression;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JConditionalExpression;
import org.multijava.mjc.JConditionalOrExpression;
import org.multijava.mjc.JDivideExpression;
import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExplicitConstructorInvocation;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JMinusExpression;
import org.multijava.mjc.JModuloExpression;
import org.multijava.mjc.JMultExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNewAnonymousClassExpression;
import org.multijava.mjc.JNewArrayExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JPostfixExpression;
import org.multijava.mjc.JPrefixExpression;
import org.multijava.mjc.JRealLiteral;
import org.multijava.mjc.JRelationalExpression;
import org.multijava.mjc.JShiftExpression;
import org.multijava.mjc.JStringLiteral;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JTypeNameExpression;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.mjc.JUnaryPromote;
import org.multijava.util.MessageDescription;
import org.multijava.util.compiler.TokenReference;

/**
 * A RAC visitor class to translate JML expressions into Java source
 * code.  The generated code is a sequence of Java statements that
 * evaluate the given expression and store the result into the given
 * variable. The result variable is assumed to be declared in the
 * outer scope that incorporates the code.  Both the expression to be
 * translated and the result variable is passed into as arguments of
 * the constructors of this class.
 *
 *<p> <b>Exceptions and Undefinedness</b> A Java expression can throw
 * an exception. In both mathematical and computational models, we must
 * handle the undefinedness caused by exception. Ideally, we would like
 * to deal with exceptions by having the evaluation of predicates
 * substitute an arbitrary expressible value of the normal result type
 * when an exception is thrown during evaluation [JML]. In practice,
 * however, the runtime asserton checker must determine the definite
 * value for top-level predicates to determine the truth of assertions,
 * e.g., pre- and postcondition violations. There are at least threee
 * possibilities to cope with this problem.
 * 
 * <ul><li>
 *  <em>To interpret the exception as "strict" false</em>.
 * By strictness, we means that if an expression throws an exception,
 * all its enclosing predicates including the top-most one become
 * false. In this interpretation, for example, if any subexpression of a
 * precondition throws an exception, the precondition is treated as
 * violated. 
 * </li></ul>
 *
 * <ul><li> <em>To interpret the exception as "non-strict" false</em>.
 * If an expression throws an exception, the smallest boolean
 * expression that encloses the expresseion becomes false.  The rest
 * of outer expressions are evaluated normally.  The underlying idea
 * is not to interpret an exception if it does not contribute to the
 * truth value of the top-level predicate.  But if it does, it is
 * interpreted as false. A shortcoming of this approach is that an
 * exception may contribute to making the top-level predicate
 * true. For example, the predicate <code>!E</code> becomes true if
 * the boolean valued expression <code>E</code> throw an exception.
 * </li></ul>
 *
 * <ul><li>
 *  <em>To interpret the exception as "non-strict" false or true
 * depending on the context</em>. 
 * As in the previous approach, the subexpression that throws an
 * exception is not interpreted if its result does not contribute to
 * the truth of the top-level predicate. But if it does, it is
 * interpreted in such a way to making the truth of the top-level
 * predicate false. That is, the expression must not contribute to
 * interpreting the top-level predicate true.
 * </li></ul>
 *
 * In this implementation, we take the third approach --- the
 * context-sensitive non-strict interpretation. The idea is to
 * ignore an exception as long as it does not affect the evaluation of
 * the top-level predicate, and, if it does, to let the exception
 * contribute to the evaluation toward making the predicate false,
 * but not true.
 *
 * <p> <b>Nonexecutable Expressions</b> A nonexecutable expression
 * poses a similar problem, and we take a similar approach. But in
 * this case, we take an angelic view. That is, a nonexecutable
 * subexpression is not interpreted if its result does not contribute
 * the truth of the top-level predicate. But if it does, it is
 * interpreted in such a way to making the truth of the top-level
 * predicate true.  For example, a precondition of the form
 * "<code>requires (* any informal description *);"</code> is
 * interpreted as being satisfied.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.104 $
 */
public class TransExpression extends AbstractExpressionTranslator {

	// FIXME - must refactor to create a better way to communicate 
	// TransUtils.genSpecTestFile into this class

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Constructs an instance and translates the given expression.
	 *
	 * @param varGen variable generator to be used for generating
	 *               fresh variable names necessary in the translated code.
	 * @param expr expression to be translated.
	 * @param resultVar variable to store the result. In the translated code,
	 *        the result of the expression is stored in the variable whose
	 *        name given by this parameter.
	 */
	public TransExpression(/*@ non_null @*/ VarGenerator varGen,
			/*@ non_null @*/ RacContext ctx,
			/*@ non_null @*/ JExpression expr,
			/*@ non_null @*/ String resultVar,
			/*@ non_null @*/ JTypeDeclarationType typeDecl) {
		this.varGen = varGen;
		this.resultVar = resultVar;
		this.expression = expr;
		this.context = ctx;
		this.typeDecl = typeDecl;
		paramStack = new Stack();
		resultStack = new Stack();
		paramStack.push(resultVar);
		translated = false;
	}

	// ----------------------------------------------------------------------
	// ACCESSORS
	// ----------------------------------------------------------------------

	/** Returns the result of translating the expression. The returned
	 * code is not wrapped in a try-catch statement that caches
	 * exceptions and non-executable specifications in the expression.
	 *
	 * <pre><jml>
	 * normal_behavior
	 *   assignable translated;
	 *   ensures \fresh(\result) && \result != null && 
	 *     (* \result is the translation result *);
	 * </jml></pre>
	 *
	 * @return translation result
	 * @see #wrappedStmt()
	 */
	public RacNode stmt() {
		perform();
		return (RacNode) resultStack.peek();
	}

	/** Returns the result of translating the expression wrapped in a
	 * try-catch statement to assign the given default values if an
	 * exception or non-executability happens while evaluating the
	 * expression. The returned code has the following structure.
	 *
	 * <pre>
	 * try {
	 *  [[E, r]]
	 * } catch (JMLNonExecutableException e) {
	 *  r = nval;
	 * } catch (Exception e) {
	 *  r = eval;
	 * }
	 * </pre>
	 *
	 * where <code>E</code> is the target expression to translate and
	 * <code>r</code> is the variable to hold the result of the expression.
	 *
	 * <pre><jml>
	 * normal_behavior
	 *   assignable translated;
	 *   ensures \fresh(\result) && \result != null && 
	 *     (* \result is a try-catch statement wrapping translation result *);
	 * </jml></pre>
	 *
	 * @param eval default value for exceptions. 
	 *        If the given expression (or one of its subexpressions) throws an
	 *        exception during evaluation, the value given by this parameter
	 *        is used as the result.
	 * @param nval default value for non-executable expressions.
	 * @return translation result wrapped in a try-catach block
	 * @see #stmt()
	 */
	public RacNode wrappedStmt(/*@ non_null @*/ String eval, 
			/*@ non_null @*/ String nval) {
		perform();
		RacNode stmt = RacParser.parseStatement(
				"try {\n" +
				"$0\n" +
				"}\n" +
				"catch (JMLNonExecutableException jml$e99) {\n" +
				"  $1 = " + nval + ";\n" +
				"}" +
				"catch (java.lang.Exception jml$e99) {\n" +
				"  $1 = " + eval + ";\n" +
				"}", 
				((RacNode)resultStack.peek()).incrIndent(), resultVar);
		return stmt;
	}

	/** Translates the current expression into a sequence of Java
	 * statements that evaluate and store the result in the result
	 * variable.  The result variable is assumed to be declared in the
	 * outer scope.
	 *
	 * <pre><jml>
	 *   requires !translated;
	 *   assignable translated;
	 *   ensures translated && (* translation is performed *);
	 * also
	 *   requires translated;
	 *   ensures (* no translation is performed *);
	 * </jml></pre>
	 */
	protected void perform() {
		if (!translated) {
			translated = true;
			expression.accept(this);
		}
	}

	// ----------------------------------------------------------------------
	// VISITORS FOR TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translates the given RAC predicate, a refinement of JML
	 * predicate.  The translation rule for this expression is defined
	 * as follows.
	 *
	 * <pre>
	 *   [[P, r]] =
	 *     [[expr(P), r]]
	 *     if (!r) {
	 *        VN_ERROR_SET.add(loc(P));
	 *     }
	 * </pre>
	 *
	 * where <code>expr(P)</code> denotes the unwrapped JML
	 * specification expression of <code>P</code>,
	 * <code>VN_ERROR_SET</code> is a variable name for keeping track
	 * of violated assertions and <code>loc(P)</code> denotes the
	 * location that the predicate <code>P</code> appears in the
	 * source file.
	 */
	public void visitRacPredicate(RacPredicate self) {
		String var = PEEK_ARGUMENT();

		// translate spec expression
		initDiagTerms();
		self.specExpression().accept(this);

		TokenReference tref = self.getTokenReference();
		if (tref == null)
			tref = self.specExpression().getTokenReference();
		if (tref != TokenReference.NO_REF) {

			String msg = escapeString(tref.toString());
			String msg1 = msg;
			if (self.hasMessage()) {
				msg = escapeString(self.message()) + "(" + msg + ")";
			}
			//msg = "\"\\t" + msg; // opening double quote with tab
			msg = "\"" + msg; // opening double quote with tab

			String dterms = "";
			if (hasDiagTerms()) {
				String dvar = varGen.freshVar();
				dterms = diagTerms(dvar);
				msg += " when\" + " + dvar;
			} else {
				msg += "\""; // closing double quote
			}

			RacNode stmt = (RacNode) GET_RESULT();
			stmt = RacParser.parseStatement(
					"$0\n" +
					(self.countCoverage ? 
							"JMLChecker.addCoverage(\"" + msg1 + "\"," + var + ");\n"
							: "") +
							"if (!" + var + ") {\n" +
							dterms +
							"  " + VN_ERROR_SET + ".add(" + msg + ");\n" +
							"}", stmt);
			RETURN_RESULT(stmt);
		}
	}

	/**
	 * Translates the given JML predicate. The translation rule for
	 * this expression is defined as follows.
	 *
	 * <pre>
	 *   [[P, r]] = [[expr(P), r]]
	 * </pre>
	 *
	 * where <code>expr(P)</code> denotes the unwrapped JML
	 * specification expression of <code>P</code>.
	 */
	public void visitJmlPredicate(JmlPredicate self) {
		//Debug.initialize(true);
		//Debug.setPrefix("TransPred");
		//Debug.msg("In JmlPredicate");

		self.specExpression().accept(this);

		//Debug.initialize(false);
	}

	/**
	 * Translates a JML specification expression. The translation rule 
	 * for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[E, r]] = [[expr(E), r]]
	 * </pre>
	 *
	 * where <code>expr(E)</code> denotes the unwrapped Java
	 * expression of <code>E</code>.
	 */
	public void visitJmlSpecExpression(JmlSpecExpression self) {
		//Debug.msg("In JmlSpecExpression: " +
		//	  self.expression().getClass().getName());

		self.expression().accept(this);
	}

	// ----------------------------------------------------------------------
	// JML PRIMARY
	// ----------------------------------------------------------------------

	/**
	 * Translates a JML <code>\nonnullelements</code> expression. The
	 * translation rule for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\nonnullelements(E), r]] =
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     r = v != null;
	 *     if (r) {
	 *        for (int i = 0; r && i < v.length; i++) {
	 *            r = v[i] != null;
	 *        }
	 *     }
	 * </pre>
	 *
	 * where <code>T_E</code> is the type of expression <code>E</code>
	 * and <code>d_T_E</code> is the default value of the type
	 * <code>T_E</code>.
	 */
	public void visitJmlNonNullElementsExpression(
			JmlNonNullElementsExpression self ) {

		//Debug.msg("In JmlNonNullElementsExpression");

		String resultVar = (String) paramStack.pop();
		JmlSpecExpression expr = self.specExpression();

		// trivially hold if base type is primitive
		if (((CArrayType)expr.getApparentType()).getBaseType().isPrimitive()) {
			resultStack.push(RacParser.parseStatement(resultVar + " = true;"));
			return;
		}

		// translate the expression to get an array object
		String var = freshVar();
		paramStack.push(var);
		expr.accept(this);
		RacNode stmt = (RacNode) resultStack.pop();

		stmt = RacParser.parseStatement(
				toString(expr.getApparentType()) + " " + var + " = null;\n" + 
				"$0\n" +
				resultVar + " = " + var + " != null;\n" +
				"for (int i = 0; " + resultVar + " && i < " + var + 
				".length; i++)\n" +
				"  " + resultVar + " = " + var + "[i] != null;", stmt);
		resultStack.push(stmt);
	}

	/**
	 * Translates the given JML <code>\elemtype</code> expression. The
	 * translation rule for this expression is defined as follows
	 * (thanks to Erik Poll) - adjusted DRC.
	 *
	 * <pre>
	 *   [[\elemtype(E)), r]] = 
	 *     r = [[E]].getComponentType();
	 * </pre>
	 */
	public void visitJmlElemTypeExpression( JmlElemTypeExpression self ) {
		JmlSpecExpression expr = self.specExpression();

		// code for evaluating the expression; it is guaranteed to be
		// non-"null" expression by the typechecker.
		String var = varGen.freshVar();
		RacNode node = translate(expr, var);

		String resultVar = GET_ARGUMENT();
		RacNode result = RacParser.parseStatement(
				toString(expr.getApparentType()) + " " + var + " = null;\n" + 
				"$0\n" +
				resultVar + " = " + var + ".getComponentType();",
				node);
		RETURN_RESULT(result);
	}

	/**
	 * Translates a JML <code>\not_modified</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\not_modified(E)), r]] = \not_executable
	 * </pre>
	 */
	public void visitJmlNotModifiedExpression( 
			JmlNotModifiedExpression self ) {

		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The expression \\not_modified");

		booleanNonExecutableExpression();
	}

	/**
	 * Translates a JML <code>\not_assigned</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\not_assigned(E)), r]] = \not_executable
	 * </pre>
	 */
	public void visitJmlNotAssignedExpression( 
			JmlNotAssignedExpression self ) {

		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The expression \\not_assigned");

		booleanNonExecutableExpression();
	}

	/**
	 * Translates a JML <code>\fresh</code> expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\fresh(E)), r]] = \not_executable
	 * </pre>
	 */
	public void visitJmlFreshExpression( JmlFreshExpression self ) {

		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The expression \\fresh");

		booleanNonExecutableExpression();
	}

	/**
	 * Translates a JML informal description expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[(* ... *), r]] = \not_executable
	 * </pre>
	 */
	public void visitJmlInformalExpression( JmlInformalExpression self ) {
		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The informal description");

		booleanNonExecutableExpression();
	}

	/**
	 * Translates a JML <code>invariant_for</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\invariant_for(E), r]] = 
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     r = v.inv();
	 * </pre>
	 *
	 * where <code>inv()</code> is the invariant method of type
	 * <code>T_E</code>.  A special treatment is required if
	 * <code>v</code> is <code>null</code>.
	 */
//	public void visitJmlInvariantForExpression( 
//	JmlInvariantForExpression self ) {

//	// indicate that the specification inheritance method
//	// (rac$check) is needed.
//	TransType.specInheritanceMethodNeeded = true;

//	// code for evaluating the expression
//	JmlSpecExpression expr = self.specExpression();
//	String var = varGen.freshVar();
//	RacNode exprEval = translate(expr, var);

//	// code for dynamically calling invariant check method
//	String resultVar = GET_ARGUMENT();
//	CType type = expr.getApparentType();
//	CClass clazz = type.getCClass();
//	String evar = varGen.freshVar();
//	RacNode invCall = RacParser.parseStatement(
//	"try {\n" +
//	"  rac$check(\"" +TransUtils.dynamicCallName(clazz)+ 
//	"\", (JMLCheckable)" +var+ ",\n" +
//	"    \"" +TransUtils.invariantLikeName(MN_CHECK_INV,clazz,false)+
//	"\",\n" +
//	"    new java.lang.Class[] { java.lang.String.class },\n"+
//	"    new java.lang.Object[] { null });\n" +
//	"  " + resultVar + " = true;\n" +
//	"} catch (JMLAssertionError " + evar + ") {\n" +
//	"  " + resultVar + " = false;\n" +
//	"}");

//	// combine code for evaluating expression and calling inv method
//	RacNode result = RacParser.parseStatement(
//	toString(type) + " " + var + " = null;\n" + 
//	"$0\n" +
//	"if (" + var + " != null) {\n" +
//	"  if (" + var + " instanceof JMLCheckable) {\n" +
//	"$1\n" +
//	"  } else {\n" +
//	"    throw JMLChecker.ANGELIC_EXCEPTION;\n" + 
//	"  }\n" +
//	"} else {\n" +
//	"  throw JMLChecker.DEMONIC_EXCEPTION;\n" + 
//	"}",
//	exprEval, invCall.incrIndent().incrIndent());

//	// guard against undefinedness
//	result = guardUndefined(context, result, resultVar);

//	RETURN_RESULT(result);
//	}

	/**
	 * Translates a JML <code>\is_initialized</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\is_initialized(T), r]] = 
	 *     try {
	 *       r = T.class.getDeclaredField(VN_RAC_COMPILED).getBoolean(null);
	 *     } catch (Exception e) {
	 *       r = true;
	 *     }
	 * </pre>
	 */
	public void visitJmlIsInitializedExpression( 
			JmlIsInitializedExpression self) {
		CType type = self.referenceType();
		String resultVar = GET_ARGUMENT();

		// interfaces are trivially assumed to be initialized.
		if (type.getCClass().isInterface()) {
			RETURN_RESULT(RacParser.parseStatement(resultVar + " = true;"));
			return;            
		}

		// for classes, check whether the jmlc-added static field,
		// VN_RAC_COMPILED, is initialized or not.
		// T.class has the side-effect of initializing the class????
		String var = varGen.freshVar();
		RacNode result = RacParser.parseStatement(
				"try {\n" +
				"  java.lang.reflect.Field " +var+ " = " +type+
				".class.getDeclaredField(\"" +VN_RAC_COMPILED+ "\");\n" +
				"  " +resultVar+ " = " +var+ ".getBoolean(null);\n" +
				"} catch (java.lang.Exception " +varGen.freshVar()+ ") {\n" +
				"  " +resultVar+ " = true;\n" + 
		"}");

		RETURN_RESULT(result);
	}

	/**
	 * Translates a JML label expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[(\lblneg n E), r]] = [[E, r]]
	 *   [[(\lblpos n E), r]] = [[E, r]]
	 * </pre>
	 * 
	 * Though not shown in the translation rule, the label of the
	 * given expression is added to VN_ERROR_SET if the expression
	 * does not (or does) hold depending on the kind of label.
	 */
	public void visitJmlLabelExpression( JmlLabelExpression self ) 
	{
		// translate the spec expression
		String var = PEEK_ARGUMENT();
		self.specExpression().accept(this);

		// build error message
		TokenReference tref = self.getTokenReference();
		String msg = "label: '" + escapeString(self.ident()) + "'(" + 
		escapeString(tref.toString()) + ")";

		RacNode stmt = (RacNode) GET_RESULT();
		stmt = RacParser.parseStatement(
				"$0\n" +
				"if (" + (self.isPosLabel() ? "" : "!") + var + ") {\n" +
				"   " + VN_ERROR_SET + ".add(\"\\t" + msg + "\");\n" +
				"}", stmt);
		RETURN_RESULT(stmt);
	}

	/**
	 * Translates a JML <code>\lockset</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\lockset, r]] = \not_executable
	 * </pre>
	 */
	public void visitJmlLockSetExpression( JmlLockSetExpression self ) {
		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The expression \\lockset");

		nonExecutableExpression();
	}

	/**
	 * Translates a JML <code>\old</code> expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\old(E), r]] = 
	 *      r = v;  
	 * </pre>
	 *
	 * with an insertion of <code>T_E v = d_T_E; [[E, v]]</code>
	 * into the method prolog.
	 *
	 * @see TransPostcondition
	 * @see TransOldExpression
	 */
	public void visitJmlOldExpression( JmlOldExpression self ) {
		if (self.getType().isBoolean()) {
			booleanNonExecutableExpression();
		} else {
			nonExecutableExpression();
		}
	}

	/**
	 * Translates a JML <code>\pre</code> expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\pre(E), r]] = 
	 *      r = v;  
	 * </pre>
	 *
	 * with an insertion of <code>T_E v = d_T_E; [[E, v]]</code>
	 * into the method prolog.
	 *
	 * @see TransPostcondition
	 * @see TransOldExpression
	 *
	 */
	public void visitJmlPreExpression( JmlPreExpression self ) {
		if (self.getType().isBoolean()) {
			booleanNonExecutableExpression();
		} else {
			nonExecutableExpression();
		}
	}

	/**
	 * Translates a JML <code>\reach</code> expression. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\reach(E), r]] = \not_executable 
	 * </pre>
	 *
	 */
	public void visitJmlReachExpression( JmlReachExpression self ) {
		warn(self.getTokenReference(), 
				RacMessages.NOT_EXECUTABLE,
				"The expression \\reach");

		nonExecutableExpression();
	}

	/**
	 * Translates a JML <code>\result</code> expression. The translation 
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[\result, r]] = 
	 *     r = result;
	 * </pre>
	 *
	 * where the variable <code>result</code> is used to capture the
	 * return value of the method. The statement <code>T result =
	 * d_T;</code> gets inserted into the method prolog, where
	 * <code>T</code> is the return type of the method.
	 *
	 * @see TransPostcondition
	 */
	public void visitJmlResultExpression( JmlResultExpression self ) {
		nonExecutableExpression();
	}

	/**
	 * Translates a JML set comprehension expression. The translation 
	 * rule for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[new S { T x | E.has(x) && P}, r]] = 
	 *     T_E c = null;
	 *     [[E, c]]
	 *     r = new S();
	 *     Iterator iter = c.iterator();
	 *     for (iter.hasNext()) {
	 *         T x = iter.next();
	 *         boolean b = false;
	 *         [[P, b]]
	 *         if (b) {
	 *            r.add(x);
	 *         }
	 *     }
	 * </pre>
	 */
	public void visitJmlSetComprehension( JmlSetComprehension self ) {
		CType type = self.getApparentType();
		CType memberType = self.memberType();
		String ident = self.ident();
		JExpression supersetPred = self.supersetPred();
		JmlPredicate predicate = self.predicate();

		// code for evaluating superset, i.e., [[E, superset]]
		String supersetVar = varGen.freshVar();
		//@ assert self.supersetPred() instanceof JMethodCallExpression;
		JMethodCallExpression supersetExpr
		= (JMethodCallExpression)supersetPred;
		JExpression prefix = supersetExpr.prefix();
		//@ assert prefix != null; // coz typechecker adds "this".
		RacNode supersetNode = translate(prefix, supersetVar);

		// code for evaluating predicate, i.e., P
		String var = varGen.freshVar();
		//@ assert self.predicate() != null;
		RacNode pred = translate(predicate, var);

		String resultVar = GET_ARGUMENT();
		String iter = varGen.freshVar(); // for iterator
		String avar = varGen.freshVar(); // for accumulating eligible elems
		String ovar = varGen.freshVar(); // for elem
		RacNode result = RacParser.parseStatement(
				resultVar + " = null;\n" +
				prefix.getApparentType() + " " + supersetVar + " = null;\n" +
				"$0\n" + // superset eval
				"java.util.HashSet " + avar + " = new java.util.HashSet();\n" +
				"java.util.Iterator " +iter+ " = " +supersetVar+ ".iterator();\n"+
				"while (" + iter + ".hasNext()) {\n" +
				"  java.lang.Object " + ovar + " = " + iter + ".next();\n" +
				"  if (!(" + ovar + " instanceof " + memberType + ")) {\n" +
				"    continue;\n" +
				"  }\n" +
				"  " + memberType + " " + ident +
				" = (" + memberType + ") " + ovar + ";\n" +
				"  boolean " + var + " = false;\n" +
				"$1\n" + 
				"  if (" + var + ") {\n" +
				"    " + avar + ".add(" + ident + ");\n" +
				"  }\n" +
				"}\n" +
				resultVar + " = " + type + ".convertFrom(" + avar + ");",
				supersetNode, pred.incrIndent());
		RETURN_RESULT(result);
	}

	/**
	 * Translates a JML quantified expression. The translation 
	 * rules for the JML universal/existential quantified expressions
	 * are defined as follows. The rules for other quantifiers are 
	 * defined in a similar way.
	 *
	 * <pre>
	 *   [[(\forall T x; P; Q), r]] =
	 *     Collection c = null;
	 *     [[S, c]]  // S is the qset of P ==> Q
	 *     r = c != null;
	 *     if (r) {
	 *        Iterator iter = c.iterator();
	 *        for (r && iter.hasNext()) {
	 *            T x = iter.next();
	 *            [[P ==> Q, r]]
	 *        }
	 *     }
	 * </pre>
	 *
	 * <pre>
	 *   [[(\exists T x; P; Q), r]] =
	 *     Collection c = null;
	 *     [[S, c]]  // S is the qset of P && Q
	 *     r = c == null;
	 *     if (!r) {
	 *        Iterator iter = c.iterator();
	 *        for (!r && iter.hasNext()) {
	 *            T x = iter.next();
	 *            [[P && Q, r]]
	 *        }
	 *     }
	 * </pre>
	 */
	public void visitJmlSpecQuantifiedExpression( 
			JmlSpecQuantifiedExpression self ) {
		TransQuantifiedExpression trans = new TransQuantifiedExpression(
				varGen, context, self, GET_ARGUMENT(), this);
		RETURN_RESULT(trans.translate());
	}

	/**
	 * Translates a JML <code>\type</code> expression. If the
	 * expression is of primitive types, the result is the Java
	 * predefined <code>Class</code> object representing the primitive
	 * type, e.g., <code>Integer.TYPE</code> for <code>int</code>.
	 * Otherwise, the following translation rule is applied.
	 *
	 * <pre>
	 *   [[\type(E), r]] = 
	 *     r = E.class;
	 * </pre>
	 */
	public void visitJmlTypeExpression( JmlTypeExpression self ) {
		CType type = self.type();
		String resultVar = GET_ARGUMENT();

		if (type.isPrimitive() || type.isVoid()) {
			RETURN_RESULT(translatePrimitiveType(type, resultVar));
		} else {
			RETURN_RESULT(RacParser.parseStatement(
					resultVar + " = " + toString(type) + ".class;"));
		}
	}

	/**
	 * Translates the given primitive type. E.g., for the type
	 * <code>int</code>, the result is "var = Integer.TYPE;".
	 *
	 * <pre><jml>
	 * requires type != null && type.isPrimitive() && var != null;
	 * ensures \result != null;
	 * </jml></pre>
	 */
	private RacNode translatePrimitiveType(CType type, String var) {
		String result = null;
		switch (type.getTypeID()) {
		case TID_BOOLEAN:
			result = "java.lang.Boolean.TYPE";
			break;
		case TID_BYTE:
			result = "java.lang.Byte.TYPE";
			break;
		case TID_CHAR:
			result = "java.lang.Character.TYPE";
			break;
		case TID_DOUBLE:
			result = "java.lang.Double.TYPE";
			break;
		case TID_FLOAT:
			result = "java.lang.Float.TYPE";
			break;
		case TID_INT:
			result = "java.lang.Integer.TYPE";
			break;
		case TID_LONG:
			result = "java.lang.Long.TYPE";
			break;
		case TID_SHORT:
			result = "java.lang.Short.TYPE";
			break;
		case TID_VOID:
			result = "java.lang.Void.TYPE";
			break;
		default:
			//@ unreachable;
		}
		return RacParser.parseStatement(var + " = " + result + ";");
	}

	/**
	 * Translates a JML <code>\typeof</code> expression. If the
	 * expression is of primitive types, the result is the Java
	 * predefined <code>Class</code> object representing the primitive
	 * type, e.g., <code>Integer.TYPE</code> for <code>int</code>.
	 * Otherwise, the following translation rule is applied.
	 *
	 * <pre>
	 *   [[\typeof(E), r]] = 
	 *    T v;
	 *    [[E, v]]
	 *    if (v == null)
	 *      r = java.lang.Object; // !FIXME!\typeof(null)
	 *    else
	 *      r = v.getClass();
	 * </pre>
	 */
	public void visitJmlTypeOfExpression( JmlTypeOfExpression self ) {
		JmlSpecExpression expr = self.specExpression();
		CType type = expr.getType();
		String resultVar = GET_ARGUMENT();

		if (type.isPrimitive() || type.isVoid()) {
			RETURN_RESULT(translatePrimitiveType(type, resultVar));
		} else {
			// evaluate expr to determine its dynamic type.
			String v = freshVar();
			RacNode stmt = RacParser.parseStatement(
					"java.lang.Object " + v + " = null;\n" +
					"$0\n" +
					"if (" + v + " == null) {\n" +
					"  // In JML, \\typeof(null) is \"undefined\",\n" +
					"  // so we throw an exception.\n" +
					"  throw JMLChecker.DEMONIC_EXCEPTION;\n" + 
					"} else {\n" +
					"  " + resultVar + " = " + v + ".getClass();\n" +
					"}",
					translate(expr, v));
			RETURN_RESULT(stmt);
		}
	}

	public void visitJmlMaxExpression( JmlMaxExpression self ) {
		fail("\\max expression is not supported in RAC");
	}

	// ----------------------------------------------------------------------
	// EXPRESSION SYNTAX
	// ----------------------------------------------------------------------

	/** Translates a Java assignment expression. The JML type checker
	 * gurantees that this be never visited, i.e., assignment
	 * expressions are not allowed in JML expression. */
	public void visitAssignmentExpression( JAssignmentExpression self ) 
	{
		fail("Assignment expression not supported in JML");
	}

	/** Translates a Java compound assignment expression. The JML type
	 * checker gurantees that this be never visited, i.e., assignment
	 * expressions are not allowed in JML expression. */
	public void visitCompoundAssignmentExpression(JAssignmentExpression self) 
	{
		fail("Compound assignment expression not supported in JML");
	}

	/**
	 * Translates a Java conditional expression. The translation rule
	 * for the conditional expression is defined as follow.
	 *
	 * <pre>
	 *   [[E1 ? E2 : E3, r]] =
	 *     boolean v = false;
	 *     [[E1, v]]
	 *     if (v1) {
	 *        [[E2, r]]
	 *     }
	 *     else {
	 *        [[E3, r]]
	 *     }
	 * </pre>
	 */
	public void visitConditionalExpression( JConditionalExpression self ) 
	{
		//Debug.msg("In JConditionalExpression");

		String r = GET_ARGUMENT(); // pop result var from the param stack
		String v = freshVar();
		RacNode stmt = RacParser.parseStatement(
				"boolean " + v + " = false;\n" +
				"$0\n" +
				"if (" + v + ") {\n" +
				"$1\n" +
				"} else {\n" +
				"$2\n" +
				"}", 
				translate(self.cond(), v),
				translate(self.left(), r).incrIndent(),
				translate(self.right(), r).incrIndent());
		RETURN_RESULT(stmt); // push result to the result stack
	}

	/**
	 * Translates a JML relational expression. If the expression is a
	 * subtype-of expression, the following translation rule is used.
	 * expression.  
	 * <pre>
	 *   [[E1 <: E2, r]] =
	 *     Class v1 = null;
	 *     Class v2 = null;
	 *     [[E1, v1]]
	 *     [[E2, v2]]
	 *     r = v2.isisAssignableFrom(v1);
	 * </pre>
	 * 
	 * Otherwise (i.e., for <code><==></code>, <code><=!=></code>,
	 * <code>==></code>, and <code><==</code>, the following
	 * translation rule is used.
	 *
	 * <pre>
	 *   [[E1 op E2, r]] =
	 *     boolean v1 = false;
	 *     boolean v2 = false;
	 *     [[E1, v1]]
	 *     [[E2, v2]]
	 *     r = [[v1,v2,op]];
	 * </pre>
	 *
	 *  where the translation <code>[[v1,v2,op]]</code> is defined as
	 *  follow.
	 *
	 * <pre>
	 *   v1 <==> v2 = v1 == v2
	 *   v1 <=!=> v2 = v1 != v2
	 *   v1 ==> v2 = v1 ? v2 : true
	 *   v1 <== v2 = v2 ? v1 : true
	 * </pre>
	 *
	 * Note: there is also the case of comparing locks with < or <=
	 */
	public void visitJmlRelationalExpression(JmlRelationalExpression self) {
		if (self.isSubtypeOf()) {
			translateIsSubtypeOf(self);
			return;
		} else if (self.isEquivalence() || self.isNonEquivalence()) {
			translateEquivalence(self);
			return;
		} else if (self.isImplication() || self.isBackwardImplication()) {
			translateImplication(self);
		} else {
			// FIXME: Case of comparing locks with < or <= is not implemented
			visitRelationalExpression(self);
		}
	}

	/**
	 * Translates the given isSubtypeOf expression.
	 *
	 * <pre><jml>
	 * requires self.isSubtypeOf();
	 * </jml></pre>
	 */
	public void translateIsSubtypeOf(JmlRelationalExpression self) {
		// translate left and right expressions using local vars
		// and also record any occurrence of undefinedness.
		final String demvar = freshVar(), angvar = freshVar();
		final String lvar = freshVar(), rvar = freshVar();
		final JExpression lexpr = self.left(), rexpr = self.right();
		final RacNode lstmt = translate(lexpr, lvar, demvar, angvar);
		final RacNode rstmt = translate(rexpr, rvar, demvar, angvar);

		// compose evaluations of left and right expressions
		RacNode stmt= RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				toString(lexpr.getApparentType()) + " " + lvar + " = null;\n" +
				toString(rexpr.getApparentType()) + " " + rvar + " = null;\n" +
				"$0\n" +
				"if (!" + demvar + ") {\n" +
				"$1\n" +
				"}",
				lstmt, rstmt.incrIndent());

		final String resvar = GET_ARGUMENT();
		final String assign = resvar + " = " + 
		rvar + ".isAssignableFrom(" +lvar+ ");";
		stmt = wrapBooleanResultTC(stmt, assign, resvar, demvar, angvar);

		RETURN_RESULT(stmt);
	}


	protected RacNode wrapBooleanResult(RacNode argEval, 
			String stmt, String resVar, String demVar, String angVar) {

		return context.enabled() ?
				RacParser.parseStatement(
						"$0\n" +
						"if (" +demVar+ ") { " +
						context.demonicValue(resVar)+ "; }\n" +
						"else if (" +angVar+ ") { " +
						context.angelicValue(resVar)+ "; }\n" +
						"else {\n" +
						" " + stmt + "\n" +
						"}",
						argEval)
						:
							RacParser.parseStatement(
									"$0\n" +
									"if (" +demVar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
									"if (" +angVar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }\n" +
									stmt,
									argEval);
	}

	protected RacNode wrapBooleanResultTC(RacNode argEval, 
			String stmt, String resVar, String demVar, String angVar) {

		return context.enabled() ?
				RacParser.parseStatement(
						"$0\n" +
						"if (" +demVar+ ") { " +
						context.demonicValue(resVar)+ "; }\n" +
						"else if (" +angVar+ ") { " +
						context.angelicValue(resVar)+ "; }\n" +
						"else try {\n" +
						" " + stmt + "\n" +
						"}\n" +
						"catch (JMLNonExecutableException jml$e0) {\n" +
						"  " + context.angelicValue(resVar) + ";\n" +
						"}\n" +
						"catch (java.lang.Exception jml$e0) {\n" +
						"  " + context.demonicValue(resVar) + ";\n" +
						"}",
						argEval)
						:
							RacParser.parseStatement(
									"$0\n" +
									"if (" +demVar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
									"if (" +angVar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }\n" +
									stmt,
									argEval);
	}

	/**
	 * Translates the given logical implication expression.
	 *
	 * <pre><jml>
	 * requires self.isImplication() || self.isBackwardImplication();
	 * </jml></pre>
	 */
	public void translateImplication(JmlRelationalExpression self) {
		final String demvar = freshVar(), angvar = freshVar();
		final String lvar = freshVar(), rvar = freshVar();
		JExpression lexpr = self.left(), rexpr = self.right();
		if (self.isBackwardImplication()) {
			JExpression texpr = lexpr;
			lexpr = rexpr;
			rexpr = texpr;
		}

		// translate the left expression in the opposite context
		context.changePolarity();
		final RacNode lstmt = translate(lexpr, lvar, demvar, angvar);
		context.changePolarity();

		// translate the right expression
		final RacNode rstmt = translate(rexpr, rvar, demvar, angvar);

		// combine the result of left and right expressions.
		final String resvar = GET_ARGUMENT();
		RacNode stmt = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				"boolean " + lvar + " = false;\n" +
				"boolean " + rvar + " = false;\n" +
				"$0\n" +
				resvar + " = !" +lvar+ " && !" +demvar+  " && !" +angvar+ ";\n"+
				"if (!" + resvar + ") {\n" + 
				"$1\n" +
				"  " + resvar + " = " +rvar+ ";\n" +
				"}\n" +
				"if (!" +resvar+ ") {\n" +
				"$2\n" +
				"}\n",
				lstmt, rstmt.incrIndent(),
				checkUndefined(demvar, angvar).incrIndent());

		RETURN_RESULT(stmt);
	}

	/**
	 * Translates the given equivalence expression.
	 *
	 * <pre><jml>
	 * requires self.isEquivalence() || self.isNonEquivalence();
	 * </jml></pre>
	 */
	public void translateEquivalence(JmlRelationalExpression self) {
		final String demvar = freshVar(), angvar = freshVar();
		final String lvar = freshVar(), rvar = freshVar();
		final JExpression lexpr = self.left(), rexpr = self.right();

		// diable contextual interpretation during the translation of
		// left and right-hand-side expressions.
		final boolean enabled = context.enabled();
		context.disable();

		final RacNode lstmt = translate(lexpr, lvar, demvar, angvar);
		final RacNode rstmt = translate(rexpr, rvar, demvar, angvar);

		// restore the contextual interpretation status
		context.setEnabled(enabled);

		// combine the result of left and right expressions.
		RacNode stmt = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				"boolean " + lvar + " = false;\n" +
				"boolean " + rvar + " = false;\n" +
				"$0\n" +
				"if (!" + demvar + ") {\n" +
				"$1\n" +
				"}",
				lstmt, rstmt.incrIndent());
		final String resvar = GET_ARGUMENT();
		final String body = self.isEquivalence() ?
				resvar + " = " + lvar + " == " + rvar + ";" :
					resvar + " = " + lvar + " != " + rvar + ";";
		stmt = wrapBooleanResult(stmt, body, resvar, demvar, angvar);

		RETURN_RESULT(stmt);
	}

	/**
	 * Translates a Java logical AND expression (<code>&&</code>). The
	 * translation rule for the logical AND expression is defined as
	 * follow.
	 *
	 * <pre>
	 *   [[E1 && E2, r]] =
	 *     [[E1, r]]
	 *     if (r) {
	 *        [[E2, r]]
	 *     }
	 * </pre>
	 */

	public void
	visitConditionalAndExpression( JConditionalAndExpression self ) 
	{
		//Debug.msg("In JConditionalAndExpression");

		// translate and combine left and right expressions
		String resVar = freshVar(), demVar = freshVar(), angVar = freshVar();
		RacNode n1 = translate(self.left(), resVar, demVar, angVar);
		RacNode n2 = translate(self.right(), resVar, demVar, angVar);
		n1 = RacParser.parseStatement(
				"// eval of &&\n" +
				"boolean " + resVar + " = true;\n" +
				"boolean " + demVar + " = false, " + angVar + " = false;\n" +
				"// arg 1 of &&\n" +
				"$0\n" +
				"if (" +resVar+ ") {\n" +
				"  // arg 2 of &&\n" +
				"$1\n" +
				"}\n" +
				"if (" +resVar+ ") {\n" +
				"$2\n" +
				"}\n" +
				GET_ARGUMENT() + " = " + resVar + ";",
				n1, n2.incrIndent(), checkUndefined(demVar, angVar).incrIndent());

		RETURN_RESULT(n1);	
	}

	private RacNode checkUndefined(String demvar, String angvar) {
		return RacParser.parseStatement(
				"if (" +demvar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
				"if (" +angvar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }");
	}

	/**
	 * Translates a Java logical OR expression (<code>||</code>). The
	 * translation rule for the logical OR expression is defined as
	 * follow.
	 *
	 * <pre>
	 *   [[E1 || E2, r]] =
	 *     [[E1, r]]
	 *     if (!r) {
	 *        [[E2, r]]
	 *     }
	 * </pre>
	 */
	public void 
	visitConditionalOrExpression( JConditionalOrExpression self ) 
	{
		//Debug.msg("In JConditionalOrExpression");

		//+dk:neutralContext
		boolean enabled=true;
//		if(Main.aRacOptions.neutralContext()) {
//			// disable contextual interpretation during translation of
//			// left and right-hand-side expressions.
//			enabled = context.enabled();
//			context.disable();
//		}
		//-dk:neutralContext

		// translate and combine left and right expressions
		// translate and combine left and right expressions
		String resVar = freshVar(), demVar = freshVar(), angVar = freshVar();
		RacNode n1 = translate(self.left(), resVar, demVar, angVar);
		RacNode n2 = translate(self.right(), resVar, demVar, angVar);

		//+dk:neutralContext
//		if(Main.aRacOptions.neutralContext()) {
//			// restore the contextual interpretation status
//			context.setEnabled(enabled);
//		}
		//-dk:neutralContext

		n1 = RacParser.parseStatement(
				"// eval of ||\n" +
				"boolean " + resVar + " = false;\n" +
				"boolean " + demVar + " = false, " + angVar + " = false;\n" +
				"// arg 1 of ||\n" +
				"$0\n" +
				"if (!" +resVar+ ") {\n" +
				"  // arg 2 of ||\n" +
				"$1\n" +
				"}\n" +
				"if (!" +resVar+ ") {\n" +
				"$2\n" +
				"}\n" +
				GET_ARGUMENT() + " = " + resVar + ";",
				n1, n2.incrIndent(), checkUndefined(demVar, angVar).incrIndent());

		//+dk:neutralContext
//		if(Main.aRacOptions.neutralContext()) {
//			// guard against the potential undefinedness: insert try block.
//			n1 = guardUndefined(context, n1, resultVar);
//		}
		//-dk:neutralContext

		RETURN_RESULT(n1);	
	}

	/**
	 * Translates a Java bitwise AND, OR or XOR expression (<tt>|</tt>, 
	 * <tt>&</tt> and <tt>^</tt>). The translation rule for the bitwise
	 * expression is defined as follow.
	 *
	 * <pre>
	 *   [[E1 opr E2, r]] =
	 *     T_E1 v1 = d_T_E1;
	 *     T_E2 v2 = d_T_E2;
	 *     [[E1, v1]]
	 *     [[E2, v2]]
	 *     r = v1 opr v2;
	 * </pre>
	 */
	public void visitBitwiseExpression( JBitwiseExpression self ) 
	{
		//Debug.msg("In JBitWiseExpression");

		String oper = null;
		switch (self.oper()) {
		case OPE_BAND:
			oper = " & ";
			break;
		case OPE_BOR:
			oper = " | ";
			break;
		case OPE_BXOR:
			oper = " ^ ";
			break;
		default:
			fail();
		}

		visitBinaryExpression( self, oper );
	}

	/**
	 * Translates an equality expression. The translation rule for the
	 * equality expression is defined as follows.
	 *
	 * <pre>
	 *   [[E1 opr E2, r]] =
	 *     T_E1 v1 = d_T_E1;
	 *     T_E2 v2 = d_T_E2;
	 *     [[E1, v1]]
	 *     [[E2, v2]]
	 *     r = v1 opr v2;
	 * </pre>
	 */
	public void visitEqualityExpression( JEqualityExpression self ) 
	{
		//Debug.msg("In JEqualityExpression");

		// diable contextual interpretation during translation of
		// left and right-hand-side expressions.
		final boolean enabled = context.enabled();
		context.disable();

		// evaluate left if non-null expr
		String demvar = freshVar(), angvar = freshVar();
		JExpression left = self.left();
		String v1 = "null";
		String s1 = "";
		RacNode n1 = null;
		if (left.getApparentType() != CStdType.Null) {
			v1 = freshVar();
			n1 = translate(left, v1, demvar, angvar);
			s1 = toString(left.getApparentType()) + " " + v1 + 
			" = " + defaultValue(left.getApparentType()) + ";\n" +
			"$0\n";
		}

		// evaluate right if non-null expr
		JExpression right = self.right();
		String v2 = "null";
		String s2 = "";
		RacNode n2 = null;
		if (right.getApparentType() != CStdType.Null) {
			v2 = freshVar();
			n2 = translate(right, v2, demvar, angvar);
			s2 = toString(right.getApparentType()) + " " + v2 + 
			" = " + defaultValue(right.getApparentType()) + ";\n" +
			"if (!" + demvar + ") {\n" +
			"$1\n"+
			"}";
			n2.incrIndent();
		}	

		// restore the contextual interpretation status
		context.setEnabled(enabled);

		// combine left and right evaluation
		n1 = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				s1 +
				s2,
				n1, n2);

		final String resvar = GET_ARGUMENT();
		final String oper = (self.oper() == OPE_EQ) ? " == " : " != ";
		final String stmt = resvar + " = " + 
		applyOperator( v1, v2, oper, left.getApparentType() ) + ";";

		n1 = wrapBooleanResult(n1, stmt, resvar, demvar, angvar);

		RETURN_RESULT(n1); 
	}

	/**
	 * Returns a string that represents the Java code that applies the given
	 * operator, <code>binOp</code>, to the given operands, v1 and v2.  This
	 * method handles both relational and arithmetic operators. When
	 * <code>type</code> is not Bigint this is simple: e.g. with "+", "1" and
	 * "2" as values for binOp, v1 and v2 respectively, the return value will
	 * be "1 + 2".  Special treatment is done to appropriately handle Bigint
	 * expressions -- e.g. for addition the equivalent of "v1.add(v2)" is
	 * returned.
	 *
	 * @see TransExpression#visitBinaryExpression
	 */
	public static String applyOperator(String v1, String v2, String binOp,
			CType type)
	{
		String strRet = "";
		String oper = binOp.trim();

		if(type == JmlStdType.Bigint) {
			String[] strArray = TransUtils.applyBigintBinOperator(oper);
			strRet = v1 + strArray[0] + v2 + strArray[1];
		}else { // FIXME, here should take care of real
			strRet = v1 + oper + v2;
		}

		return strRet;
	}

	/**
	 * Translates a Java relational expression (<tt><</tt>, 
	 * <tt><=</tt>, <tt>></tt>, or <tt>>=</tt>). The translation rule
	 * for the relational expression is defined as follow.
	 *
	 * <pre>
	 *   [[E1 opr E2, r]] =
	 *     try {
	 *       T_E1 v1 = d_T_E1;
	 *       T_E2 v2 = d_T_E2;
	 *       [[E1, v1]]
	 *       [[E2, v2]]
	 *       r = v1 opr v2;
	 *     }
	 *     catch (Exception e) {
	 *       r = false;
	 *     }
	 * </pre>
	 */
	public void visitRelationalExpression( JRelationalExpression self ) 
	{
		//Debug.msg("In JRelationalExpression");

		String oper = null;
		switch (self.oper()) {
		case OPE_LT:
			oper = " < ";
			break;
		case OPE_LE:
			oper = " <= ";
			break;
		case OPE_GT:
			oper = " > ";
			break;
		case OPE_GE:
			oper = " >= ";
			break;
		default:
			fail();
		}

		visitBooleanBinaryExpression( self, oper );
		RacNode n = (RacNode) resultStack.pop();
		RETURN_RESULT(n);
	}

	/**
	 * Translates a Java instanceof expression. The translation rule
	 * for the instanceof expression is defined as follow.
	 *
	 * <pre>
	 *   [[E1 instanceof T, r]] =
	 *     try {
	 *       T_E1 v = d_T_E1;
	 *       [[E1, v]]
	 *       r = v instanceof T;
	 *     }
	 *     catch (Exception e) {
	 *       r = false;
	 *     }
	 * </pre>
	 */
	public void visitInstanceofExpression( JInstanceofExpression self ) 
	{
		//Debug.msg("In JInstanceOfExpression");

		// evaluate expr if non-null
		JExpression expr = self.expr();
		String v = "null";
		String s = "";
		RacNode n = null;
		if (expr.getApparentType() != CStdType.Null) {
			v = freshVar();
			n = translate(expr, v);
			s = toString(expr.getApparentType()) + " " + v + 
			" = " + defaultValue(expr.getApparentType()) + ";\n" +
			"$0\n";
		}

		String resultVar = GET_ARGUMENT();
		CType dest = self.dest();
		n = RacParser.parseStatement(
				s + 
				resultVar + " = " + v + " instanceof " + dest + ";", n);
		n = guardUndefined(context, n, resultVar);

		RETURN_RESULT(n);
	}


	/**
	 * Translates a binary expression of the given operator.
	 */
	protected void visitBinaryExpression(JBinaryExpression self, String oper) 
	{
		String demvar = freshVar(), angvar = freshVar();
		String v1 = freshVar();
		String v2 = freshVar();
		JExpression left = self.left();
		JExpression right = self.right();

		//+dk:neutralContext
		boolean enabled=true, bNecessary=false;
		bNecessary = oper.trim().equals("|")
		&& (left.getApparentType() == CStdType.Boolean);
//		if(Main.aRacOptions.neutralContext() && bNecessary) {
//			// disable contextual interpretation during translation of
//			// left and right-hand-side expressions.
//			enabled = context.enabled();
//			context.disable();
//		}
		//-dk:neutralContext

		RacNode n1 = translate(left, v1, demvar, angvar);
		RacNode n2 = translate(right, v2, demvar, angvar);

		//+dk:neutralContext
//		if(Main.aRacOptions.neutralContext() && bNecessary) {
//			// restore the contextual interpretation status
//			context.setEnabled(enabled);
//		}
		//-dk:neutralContext

		n1 = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				toString(left.getApparentType()) + " " + v1 + 
				" = " + defaultValue(left.getApparentType()) + ";\n" +
				toString(right.getApparentType()) + " " + v2 + 
				" = " + defaultValue(right.getApparentType()) + ";\n" +
				"$0\n" +
				"if (!" + demvar + ") {\n" +
				"$1\n" +
				"}\n" +
				"if (" +demvar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
				"if (" +angvar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }\n" +
				GET_ARGUMENT() + " = " + 
				applyOperator( v1, v2, oper, left.getApparentType() ) + ";",
				n1, n2.incrIndent());

		//+dk:neutralContext
//		if(Main.aRacOptions.neutralContext() && bNecessary) {
//			// guard against the potential undefinedness: insert try block.
//			n1 = guardUndefined(context, n1, resultVar);
//		}
		//-dk:neutralContext

		RETURN_RESULT(n1);
	}

	/**
	 * Translates a binary expression of the given operator.
	 */
	protected void visitBooleanBinaryExpression(JBinaryExpression self, 
			String oper) 
	{
		final String demvar = freshVar(), angvar = freshVar();
		final String v1 = freshVar(), v2 = freshVar();
		final JExpression left = self.left(), right = self.right();

		RacNode n1 = translate(left, v1, demvar, angvar);
		RacNode n2 = translate(right, v2, demvar, angvar);

		n1 = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				toString(left.getApparentType()) + " " + v1 + 
				" = " + defaultValue(left.getApparentType()) + ";\n" +
				toString(right.getApparentType()) + " " + v2 + 
				" = " + defaultValue(right.getApparentType()) + ";\n" +
				"$0\n" +
				"if (!" + demvar + ") {\n" +
				"$1\n" +
				"}",
				n1, n2.incrIndent());


		String resvar = GET_ARGUMENT();
		String body = resvar +  " = " + 
		applyOperator(v1, v2, oper, left.getApparentType()) + ";";
		n1 = wrapBooleanResultTC(n1, body, resvar, demvar, angvar);

		RETURN_RESULT(n1);
	}

	/**
	 * Translates an add expression.
	 */
	public void visitAddExpression( JAddExpression self ) {
		visitBinaryExpression( self, " + " );
	}

	/**
	 * Translates a minus expression.
	 */
	public void visitMinusExpression( JMinusExpression self ) {
		visitBinaryExpression( self, " - " );
	}

	/**
	 * Translates a multiplication expression.
	 */
	public void visitMultExpression( JMultExpression self ) {
		visitBinaryExpression( self, " * " );
	}

	/**
	 * Translates a divide expression.
	 */
	public void visitDivideExpression( JDivideExpression self ) {
		visitBinaryExpression( self, " / " );
	}

	/**
	 * Translates a modulo division expression.
	 */
	public void visitModuloExpression( JModuloExpression self ) {
		visitBinaryExpression( self, " % " );
	}

	/**
	 * Translates a shift expression.
	 */
	public void visitShiftExpression( JShiftExpression self ) 
	{
		String opStr = null;
		int oper = self.oper();
		if (oper == OPE_SL) {
			opStr = " << ";
		} else if (oper == OPE_SR) {
			opStr = " >> ";
		} else {
			opStr = " >>> ";
		}
		visitBinaryExpression( self, opStr );
	}

	/** Translates a Java prefix expression. The JML type checker
	 * gurantees that this be never visited, i.e., prefix expressions
	 * are not allowed in JML expression. */
	public void visitPrefixExpression( JPrefixExpression self ) {
		fail("Prefix expression not supported in JML");
	}

	/** Translates a Java postfix expression. The JML type checker
	 * gurantees that this be never visited, i.e., postfix expressions
	 * are not allowed in JML expression. */
	public void visitPostfixExpression( JPostfixExpression self ) {
		fail("Postfix expression not supported in JML");
	}

	/**
	 * Translates a Java unary expression.  These are (<code>+</code>,
	 * <code>-</code>, <code>~</code>, and <code>!</code>. The
	 * translation rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[opr E, r]] = 
	 *      [[E, r]]
	 *      r = opr r;
	 * </pre>
	 * 
	 * We need a special treatment for the operator <code>!<code> to change
	 * the default return value used if there occurrs an exception while
	 * evaluating a subexpression.
	 * 
	 */
	public void visitUnaryExpression( JUnaryExpression self ) 
	{
		String oper = null;
		CType bckup = null;
		switch (self.oper()) {
		case OPE_PLUS:
			oper = "+";
			bckup = CStdType.Integer;
			break;
		case OPE_MINUS:
			oper = "-";
			bckup = CStdType.Integer;
			break;
		case OPE_BNOT:
			oper = "~";
			bckup = CStdType.Byte;
			break;
		case OPE_LNOT:
			oper = "!";
			bckup = CStdType.Boolean;
			break;
		default:
			fail("Unknown unary expression");
		}

		JExpression expr = self.expr();
		String v = freshVar();
		RacNode result = null;

		// if LNOT, translate expr in the opposite context
		if (self.oper() == OPE_LNOT) {
			context.changePolarity();
			result = translate(expr, v);
			context.changePolarity();
		} else {
			result = translate(expr, v);
		}

		CType expT = expr.getApparentType();
		if(expT == null){expT=bckup;}
		result = RacParser.parseStatement(
				toString(expT) + " " + v + 
				" = " + defaultValue(expT) + ";\n" +
				"$0\n" +
				GET_ARGUMENT() + " = " + 
				applyOperator(v, oper, expT) + ";",
				result);
		RETURN_RESULT(result);
	}

	/**
	 * Returns a string that represents the Java code that applies the given
	 * operator, <code>unaryOp</code>, to the given operand <code>v1</code>.
	 *
	 * @see TransExpression#applyOperator(String v1, String v2, String
	 * binOp, CType type)
	 * @see TransExpression#visitUnaryExpression
	 */
	public static String applyOperator(String v, String unaryOp, CType type)
	{
		String strRet= "";
		String oper = unaryOp.trim();

		if( oper.equals("+") ) {
			strRet = v;
		} else if( oper.equals("!") ) {
			strRet = oper + v;
		} else if(type == JmlStdType.Bigint) {
			strRet = v + TransUtils.applyBigintUnOperator(oper);
		} else {
			strRet = oper + v;
		}

		return strRet;
	}

	/**
	 * Translates a Java cast expression. The translation rules for this 
	 * expression is defined as follows.
	 *
	 * <pre>
	 *   [[(T) E, r]] = 
	 *      T_E v = d_T_E;
	 *      [[E, v]]
	 *      r = (T) v;
	 * </pre>
	 */
	public void visitCastExpression( JCastExpression self ) 
	{
		CType dest = self.getApparentType();
		JExpression expr = self.expr();
		RacNode n = null;
		if (expr.getApparentType() == CStdType.Null) {
			n = RacParser.parseStatement(
					GET_ARGUMENT() + " = (" + toString(dest) + ") null;");
		} else {
			String v = freshVar();
			n = translate(expr, v);
			n = RacParser.parseStatement(
					toString(expr.getApparentType()) + " " + v + 
					" = " + defaultValue(expr.getApparentType()) + ";\n" +
					"$0\n" +
					GET_ARGUMENT() + " = " +
					applyCast(v, dest, expr.getApparentType()) + ";",
					n);
		}
		RETURN_RESULT(n);
	}


	/**
	 * Returns a string that represents the Java code that casts <code>v</code>
	 * of type <code>typeVar</code> to <code>typeDest</code>.
	 *
	 * @see TransExpression#visitCastExpression
	 */
	public String applyCast(String v, CType typeDest, CType typeVar)
	{
		String strRet;
		String[] strArray;

		strArray = 
			TransUtils.applyBigintCast(typeDest, typeVar, toString(typeDest));
		strRet = strArray[0] + v + strArray[1];

		return strRet;
	}


	/**
	 * Translates a Java unary promotion expression.
	 */
	public void visitUnaryPromoteExpression( JUnaryPromote self ) {
		JExpression expr = self.expr();

		CType typeSelf = self.getApparentType();
		CType typeExpr = expr.getApparentType();

		if( !self.isCheckNeeded() && 
				!( (typeSelf == JmlStdType.Bigint) 
						&& (typeExpr != JmlStdType.Bigint) ) ) {
			expr.accept( this );
			return;
		}

		CType type = expr.getApparentType();
		String v = freshVar();
		RacNode n = translate(expr, v);
		n = RacParser.parseStatement(
				toString(type) + " " + v + " = " + defaultValue(type) + ";\n" +
				"$0\n" +
				GET_ARGUMENT() + " = " +
				TransUtils.applyUnaryPromoteExpression(typeSelf,typeExpr,v) + ";",
				n);

		RETURN_RESULT(n);
	}


	/**
	 * Translates a Java method call expression. The general
	 * translation rule for the java method call expression is defined
	 * as follow.
	 *
	 * <pre>
	 *   [[E0.m(E1, ..., En), r]] =
	 *     T_E0 v0 = d_T_E0;
	 *     T_E1 v1 = d_T_E1;
	 *     ...
	 *     T_En vn = d_T_En;
	 *     [[E0, v0]]
	 *     [[E1, v1]]
	 *     ...
	 *     [[En, vn]]
	 *     r = v0.m(v1, ..., vn);
	 * </pre>
	 *
	 * If the referenced method, <code>m</code>, is an effectively
	 * model method (including the ones declared in model types),
	 * there are three possibilities. If the method is not executable
	 * (i.e., has no body), then the method call expression is
	 * translated into an angelic undefinedness. Otherwise, the
	 * expression is translated into either a static or dynamic call
	 * to the model method. If the model method is declared in the
	 * same class or interface where the assertion being translated in
	 * specified, then static call is used; otherwise, dynamic call is
	 * used.
	 *
	 * <p> A spec_public or spec_protected method call expression is
	 * always executable, and is translated into either a dynamic or
	 * static call.
	 *
	 * @see TransType#dynamicCallNeeded(CClass)
	 * @see #translateToDynamicCall(JMethodCallExpression, boolean)
	 * @see #translateToNonexecutableCall(JMethodCallExpression)
	 * @see #tranlateToStaticCall(JMethodCallExpression, int)
	 * @see #addDiagTermThis()
	 * @see #visitNewObjectExpression(JNewObjectExpression)
	 */
	public void visitMethodCallExpression(JMethodCallExpression self) {

		// add "this" to the set of diagnostic terms for composing
		// an assertion violation message if necessary.
		JExpression prefix = self.prefix();
		if ((prefix instanceof JThisExpression) ||
				(prefix instanceof JSuperExpression)) {
			addDiagTermThis();
		}

		// handle model/spec_public/spec_protected method calls
		CMethod meth = self.method();
		if (meth instanceof JmlSourceMethod) { // is source available?
			JmlSourceMethod cmeth = (JmlSourceMethod) meth;
			if (cmeth.isEffectivelyModel()) {
				if (cmeth.isExecutableModel()) {
//					if (TransUtils.useReflection() // no -F option?
//					&& TransType.dynamicCallNeeded(meth.owner())) {
//					// true for model method calls
//					translateToDynamicCall(self, true);
//					} else {
					// translate into static model method calls
					translateToStaticCall(self, ACC_MODEL);
					//}
				} else {
					// non-executable model method calls
					warn(self.getTokenReference(), 
							RacMessages.NOT_EXECUTABLE,
							"A call to model method \"" + cmeth.ident() + "\"");

					translateToNonexecutableCall(self);
				} 
				return; // done with model method calls

			} else if (cmeth.isSpecPublic() || cmeth.isSpecProtected()) {
//				if (TransUtils.useReflection() // no -F option?
//				&& TransType.dynamicCallNeeded(meth.owner())) {
//				// true for spec_public/protected method calls
//				translateToDynamicCall(self, false);
//				} else {
				translateToStaticCall(self, ACC_SPEC_PUBLIC);
				//}
				return; // done with spec_public method calls
			}
			// regular method calls with source are translated into 
			// static method calls below.
		}

		// code making static call for normal method calls
		translateToStaticCall(self, 0);
	}

	/** Translates the given (model) method call into a non-executable
	 * method call.
	 *
	 * @see #visitMethodCallExpression(JMethodCallExpression)
	 */
	private void translateToNonexecutableCall(JMethodCallExpression expr) {
		if (context.enabled() 
				&& (expr.getApparentType().isBoolean())) {
			String var = GET_ARGUMENT();
			RacNode result = RacParser.parseStatement(
					"// from non-executable method call (e.g., model method) [" + 
					expr.method().ident() + "]\n" +
					context.angelicValue(var) + ";\n");
			RETURN_RESULT(result);
		} else {
			nonExecutableExpression();
		}
	}

	/** Translates the given method call expression into a static
	 * call. If the argument, <code>kind</code>, is ACC_MODEL, the
	 * given expression is assumed to be a model method call
	 * expression that can be translated into a static call (e.g.,
	 * called in the same type where the method is declared). In such
	 * a case, the expression is translated into a call to the
	 * appropriate surrogate object if the called model method is
	 * declared in an interface.  If the argument, <code>kind</code>,
	 * is ACC_SPEC_PUBLIC, the given expression is assumed to be a
	 * spec_public method call expression, for which we have to call
	 * the corresponding access method. Otherwise, it is assumed to be
	 * a regular method call expression.
	 *
	 * <pre><jml>
	 * requires self != null;
	 * requires kind == ACC_MODEL || kind == ACC_SPEC_PUBLIC ||
	 *          kind == 0; 
	 * </jml></pre>
	 *
	 *
	 * @see #visitMethodCallExpression(JMethodCallExpression)
	 */
	private void translateToStaticCall(JMethodCallExpression self, long kind) {
		JExpression prefix = self.prefix();
		String ident = self.ident();
//		JExpression[] args = self.args();

		// code for evaluating arguments
		String demvar = null, angvar = null;
		if (self.args() != null && self.args().length > 1) {
			demvar = freshVar();
			angvar = freshVar();
		}
		StringAndNodePair pair = 
			argumentsForStaticCall(self.args(), demvar, angvar);
		String argStr = pair.str;  // of the form "(v1, v2, ..., vn)"
		RacNode argEval = pair.node; // v1 = E1; ...; vn = En; 

		// compose call statement E1.m(x1,..,xn).
		String var = GET_ARGUMENT();
		RacNode result = null;
		String meth = kind == ACC_SPEC_PUBLIC ?
				TransUtils.specPublicAccessorName(ident) : ident;
				if (prefix == null) {
					result = RacParser.parseStatement(optLHS(self, var) + 
							meth +argStr+ ";");
				} else {
					String format = null;
					CClass clazz = self.method().owner();
					// is interface method method?
					if (kind == ACC_MODEL && clazz.isInterface()) {
						// call to the surrogate of the prefix
						String cn = TransUtils.dynamicCallName(clazz);
						String surVar = freshVar();
						format = 
							cn + " " + surVar + " = ((" +cn+ ") " + 
							"JMLChecker.getSurrogate(\"" +cn+ 
							"\", rac$forName(\"" +cn+ "\"), $0));\n" +
							optLHS(self, var) + surVar+ "." + meth + argStr+ ";";
						result = transPrefix(prefix, format);
					} else if (prefix instanceof JTypeNameExpression && 
							kind == ACC_MODEL) {
						// call to the prefix
//						JTypeNameExpression tn = (JTypeNameExpression)prefix;
						format = optLHS(self, var) + "$0." + meth + argStr + ";";
						result = transPrefix(prefix, format);
					} else {
						// call to the prefix
						format = optLHS(self, var) + "$0." + meth + argStr + ";";
						result = transPrefix(prefix, format);
					}
				}

				// guard against the potential undefinedness
				result = guardUndefined(context, result, self.getApparentType(), var, 
						demvar, angvar);
				result = RacParser.parseStatement( "// " + meth + "(...)\n$0", result);

				// prepend argument eval statements, T1 v1 = E1; ...; Tn vn = En;
				if (argEval != null) {
					result = RacParser.parseStatement(
							"// Method call: " + meth + "(...)\n" +
							(demvar == null ? "" : 
								("boolean " +demvar+ " = false, " +angvar+ " = false;\n")) +
								"$0\n$1", 
								argEval, 
								result);
				}

				RETURN_RESULT(result);
	}

	private RacNode guardUndefined(RacContext ctx, RacNode stmt, 
			CType restype, String resvar, String demvar, String angvar)
	{
		if (demvar == null) {
			if(restype!=null){
				return restype.isBoolean() ? 
						guardUndefined(ctx, stmt, resvar) : stmt;
			}else return stmt;
		}

		// contextual interpretation?
		if (restype.isBoolean() && ctx.enabled()) {
			return RacParser.parseStatement(
					"if (" +demvar+ ") { " + ctx.demonicValue(resvar) + "; }\n" +
					"else if (" +angvar+ ") { " +ctx.angelicValue(resvar)+ "; }\n"+
					"else try {\n" +
					"$0\n" +
					"}\n" +
					"catch (JMLNonExecutableException jml$e0) {\n" +
					"  " + ctx.angelicValue(resvar) + ";\n" +
					"}\n" +
					"catch (java.lang.Exception jml$e0) {\n" +
					"  " + ctx.demonicValue(resvar) + ";\n" +
					"}", stmt.incrIndent());	
		} else {
			return RacParser.parseStatement(
					"if (" +demvar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
					"if (" +angvar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }\n" +
					"$0",
					stmt);
		}
	}

	/**
	 * Returns the optional left-hand-side of assignment statement to
	 * store the result of evaluation method call expression. That is,
	 * if the type of the method call is void, an empty string is
	 * returned; otherwise, a string <code>var + " = "</code> is
	 * returned.
	 */
	private String optLHS(JMethodCallExpression expr, String var) {
		if(expr.getApparentType()==null){
			return "";
		}
		else if (expr.getApparentType().isVoid()) {
			return "";
		}
		return var + " = ";
	}

	/**
	 * Returns a pair of String and RacNode that is the translation of
	 * the given argument, <code>args</code>. The string of the pair
	 * has the form: <code>"(v1, v2, ..., vn)"</code>, and the node
	 * has the form: <code>T1 v1 = E1; ...; Tn vn = En;</code>, where
	 * <code>Ei</code> is the i-th element of the argument
	 * <code>args</code>. The variable <code>vi</code> is a fresh new
	 * variable. If the argument, <code>args</code>, is null or an
	 * empty array, the string of the pair is <code>"()"</code> and
	 * the node is null. The result is always non-null.
	 * 
	 * <pre><jml>
	 * ensures \result != null;
	 * </jml></pre>
	 */
	private StringAndNodePair argumentsForStaticCall(JExpression[] args,
			String demvar,
			String angvar) {
		// code for evaluating arguments
		String argStr = "("; // of the form "(v1, v2, ..., vn)"
		RacNode argEval = null; // v1 = E1; ...; vn = En; 
		if (args != null && args.length > 0) {
			RacNode[] n = new RacNode[args.length];
			String evalStr = "";
			for (int i = 0; i < args.length; i++) {
				if (i != 0) {
					argStr = argStr + ", ";
				}
				String v = "null";
				n[i] = null;
				if (args[i].getApparentType() != CStdType.Null) {
					if (!evalStr.equals("")) {
						evalStr = evalStr + "\n";
					}
					v = freshVar();
					evalStr = evalStr + 
					"// " + "arg " + (i + 1) + ": " + v + "\n" +
					toString(args[i].getApparentType()) + " " + v + 
					" = " + defaultValue(args[i].getApparentType())+ ";\n";
					n[i] = translate(args[i], v, demvar, angvar);
					if (demvar == null) {
						evalStr = evalStr + "$" + i;
					} else {
						evalStr = evalStr + 
						"if (!" + demvar + ") {\n  " +
						"$" + i + "\n" +
						"}";
						n[i].incrIndent();
					}
				}
				argStr = argStr + v;
			}
			argEval = evalStr.equals("") ? 
					null : RacParser.parseStatement(evalStr, n);
		}
		argStr = argStr + ")";
		return new StringAndNodePair(argStr, argEval);
	}

	/** A private data structure class for stroring a pair of String
	 * and RacNode objects. */
	private static class StringAndNodePair {
		public String str;
		public RacNode node;
		public StringAndNodePair(String str, RacNode node) {
			this.str = str;
			this.node = node;
		}
	}

	/**
	 * Translates a prefix of a field or method call expression, build
	 * a <code>RacNode</code> using the given format, and return the
	 * result.  The returned code has the following form:
	 *
	 * <pre>
	 *  T v = T_init;
	 *  [[code for eval prefix and assigning to v]]
	 *  format[v/$0]
	 * </pre>
	 *
	 * <pre><jml>
	 *  requires prefix != null && format != null;
	 *  ensures \result != null;
	 * </jml></pre>
	 *
	 * @param prefix the prefix to be translated.
	 * @param format the format to build the return value out of 
	 *               the translated prefix; it is usually of the form:
	 *               <code>"r = $0.m(x1, ..., xn);"</code> or
	 *               <code>"r = $0.f;</code>.
	 *
	 * @see #visitMethodCallExpression
	 * @see #visitFieldExpression
	 * @see #transPrefix(JExpression, String, CClass, isModel)
	 */
	protected RacNode transPrefix(JExpression prefix, String format) {
		// is the prefix a local variable?
		if (prefix instanceof JLocalVariableExpression) {
			// it may be an old variable.
			return RacParser.parseStatement(format, 
					transLocalVariable((JLocalVariableExpression) prefix));
		}

		// is the prefix a local variable, super, this (e.g., this or t.this),
		// type name, or field access (e.g., getObject().f or f)?
		if (prefix instanceof JSuperExpression ||
				(prefix instanceof JThisExpression && !TransType.isInterface()) ||
				prefix instanceof JTypeNameExpression ||
				(prefix instanceof JClassFieldExpression && // never reach here?
						((JClassFieldExpression)prefix).prefix() == null)) {
			return RacParser.parseStatement(format, prefix);
		}

		// note that in an interface, "this" should be translated into
		// the delegee field of the surrogate class; thus the
		// conjunction for the JThisExpression.

		// translate prefix and build result
		CType type = prefix.getApparentType();
		String v = freshVar();
		RacNode n = translate(prefix, v);
		return RacParser.parseStatement(
				toString(type) + " " + v + " = " + defaultValue(type) + ";\n" +
				"$1\n" +
				format, 
				v, n);
	}

	// requires genSpecTestFile;
	protected RacNode transPrefixSpec(JExpression prefix, String format, boolean addDelegee) {
		// is the prefix a local variable?
		if (prefix instanceof JLocalVariableExpression) {
			// it may be an old variable.
			return RacParser.parseStatement(format, 
					transLocalVariable((JLocalVariableExpression) prefix));
		}

		// is the prefix a local variable, super, this (e.g., this or t.this),
		// type name, or field access (e.g., getObject().f or f)?
		if (prefix instanceof JSuperExpression ||
				//(prefix instanceof JThisExpression && !TransType.isInterface()
				//			&& !genSpecTestFile) ||
				prefix instanceof JTypeNameExpression ||
				(prefix instanceof JClassFieldExpression &&
						((JClassFieldExpression)prefix).prefix() == null)) {
			return RacParser.parseStatement(format, prefix);
		}

		if (prefix instanceof JThisExpression && !TransType.isInterface() && TransType.genSpecTestFile) {
			int p = format.indexOf("$0")+2; // 2 for the length of "$0"
			if (addDelegee) format = format.substring(0,p) + ".delegee_" + typeDecl.ident() + "()" + format.substring(p);
			return RacParser.parseStatement(format, prefix);
		}

		// note that in an interface, "this" should be translated into
		// the delegee field of the surrogate class; thus the
		// conjunction for the JThisExpression.

		// translate prefix and build result
		CType type = prefix.getApparentType();
		String v = freshVar();
		RacNode n = translate(prefix, v);
		return RacParser.parseStatement(
				toString(type) + " " + v + " = " + defaultValue(type) + ";\n" +
				"$1\n" +
				format, 
				v, n);
	}


	/** Translates the given method call expression,
	 * <code>expr</code>, into a dynamic call expression. If the
	 * argument, <code>isModel</code>, is true, it is treated as a
	 * call to a model method, thus; otherwise, it is treated as a
	 * call to a spec_public or spec_protected method. This flag is
	 * used to determine appropriate access methods.
	 *
	 * @see #visitMethodCallExpression(JMethodCallExpression)
	 */
//	private void translateToDynamicCall(JMethodCallExpression expr,
//			boolean isModel) {
//		needDynamicInvocationMethod();
//
//		// decide the receiver of dynamic call
//		RacNode receiverNode = null;
//		String receiver = "";
//		if (isStatic(expr)) {
//			receiver = "null"; // null for static method
//		} else {
//			receiverNode = receiverForDynamicCall(expr);
//			receiver = (receiverNode != null) ? receiverNode.name() : "this";
//		}
//
//		// generate code for evaluating arguments; 
//		// args.node has the form: T1 v1 = E1; ...; Tn vn = En; 
//		// args.types has the form: "Class[]  = { T1, ..., Tn }" and 
//		// args.args has the form: "Object[] = { v1, ..., vn }".
//		DynamicCallArg args = argumentsForDynamicCall(
//				expr.args(), expr.method().parameters());
//		RacNode argEval = args.node;
//		String types = args.types;
//		String args2 = args.args;
//
//		// target class of dynamic call
//		CClass clazz = expr.method().owner();
//		// cn, fully qualified name of the target class
//		String cn = TransUtils.dynamicCallName(clazz);
//		// mn, the name of spec_public accessor method
//		String mn = isModel ?
//				TransUtils.modelPublicAccessorName(expr.method()) :
//					TransUtils.specPublicAccessorName(expr.method().ident());
//
//				// return code for dyanmic call to the acessor
//				String tvar = varGen.freshVar(); // for type args to the call
//				String avar = varGen.freshVar(); // for values args to the call
//				String var = varGen.freshVar();  // for holding result of the call
//				String resultVar = GET_ARGUMENT();
//				RacNode result = RacParser.parseStatement(
//						(receiverNode == null ? "" : "$0\n") + // prefix eval code
//						(argEval == null ? "" : "$1\n") +
//						"java.lang.Class[] " + tvar + " = " + types + ";\n" +
//						"java.lang.Object[] " + avar + " = " + args2 + ";\n" +
//						"java.lang.Object " + var + " = rac$invoke(\"" + cn + "\", " + 
//						receiver+ ", \"" + mn + "\", " + tvar + ", " + avar + ");\n" +
//						optLHS(expr, resultVar) + 
//						TransUtils.unwrapObject(expr.getApparentType(), var) + ";",
//						receiverNode, argEval);
//
//				// guard against the potential undefinedness
//				if (expr.getApparentType().isBoolean()) {
//					result = guardUndefined(context, result, resultVar);
//				}
//
//				RETURN_RESULT(result);
//	}

	/**
	 * Returns an object that contains information about translating
	 * arugments, <code>args</code> to a method call for making a
	 * dynamic call. The argument, <code>ptypes</code>, is supposed to
	 * be the parameter types of the called method. The field
	 * <code>node</code> of the returned object has code of the form:
	 * <code>T1 v1 = E1; ...; Tn vn = En;</code>, where
	 * <code>Ei</code> is the i-th element of the argument
	 * <code>args</code>. The field <code>types</code> has the form: "
	 * <code>"new Class[] { T1, ..., Tn }"</code>, where
	 * <code>Ti</code> is the i-th parameter type, and the field
	 * <code>args</code> has the form: <code>"new Object[] { v1, ...,
	 * vn }"."(v1, v2, ..., vn)"</code>.  The variable <code>vi</code>
	 * is a fresh new variable. If the argument, <code>args</code>, is
	 * null or an empty array, the node field becomes null and the
	 * other two fields become <code>"new Class[] {}"</code> and
	 * <code>"new Object[] {}"</code> respectively.  The result is
	 * always non-null.
	 * 
	 * <pre><jml>
	 * ensures \result != null;
	 * </jml></pre>
	 *
	 * @see #translateToDynamicCall(JMethodCallExpression, boolean)
	 * @see #translateToDynamicNewObjectExpression(JNewObjectExpression,boolean)
	 * @see #DynamicCallArg
	 */
//	private DynamicCallArg argumentsForDynamicCall(JExpression[] args,
//			CSpecializedType[] ptypes)
//	{
//		// generate code for evaluating arguments, i.e., 
//		// T1 v1 = E1; ...; Tn vn = En; 
//		RacNode argEval = null; 
//		// and also arguments for making a dynamic call, i.e.,
//		// "new Class[] { T1, ..., Tn }" and
//		// "new Object[] { v1, ..., vn }".
//		String types = null;
//		String args2 = null;
//
//		if (args != null && args.length > 0) {
//			// accumlator for evaluating aruments
//			RacNode[] accum = new RacNode[args.length];
//			String evalStr = "";
//
//			// accumlator for generating arguments to dynamic call
//			final StringBuffer tcode = new StringBuffer("{ "); // for types
//			final StringBuffer acode = new StringBuffer("{ "); // for args
//
//			for (int i = 0; i < args.length; i++) {
//				// code for evaluating arugments
//				String v = "null"; // var to hold the result of arg eval
//				accum[i] = null;
//				if (args[i].getApparentType() != CStdType.Null) {
//					if (!evalStr.equals(""))
//						evalStr = evalStr + "\n";
//					v = freshVar();
//					evalStr = evalStr + 
//					toString(args[i].getApparentType()) + " " + v + 
//					" = " + defaultValue(args[i].getApparentType())+ ";\n";
//					evalStr = evalStr + "$" + i;
//					accum[i] = translate(args[i], v);
//				}
//
//				// code for generating dynamic call arguments
//				if (i != 0) {
//					tcode.append(", ");
//					acode.append(", ");
//				}
//				CType actualType = ptypes[i].staticType();
//				tcode.append(TransUtils.typeToClass(actualType));
//				acode.append(TransUtils.wrappedValue(actualType, v) + " ");
//			}
//
//			// code for evaluating arguments
//			argEval = evalStr.equals("") ? 
//					null : RacParser.parseStatement(evalStr, accum);
//
//			// code for generating dynamic call arguments
//			tcode.append("}");
//			acode.append("}");
//			types = "new java.lang.Class[] " + tcode.toString();
//			args2 = "new java.lang.Object[] " + acode.toString();
//		}
//		return new DynamicCallArg(types, args2, argEval);
//	}

	/** A private data structure class for stroring information about
	 * arguments for dynamic calls. */
//	private static class DynamicCallArg {
//		public String types;
//		public String args;
//		public RacNode node;
//		public DynamicCallArg(String types, String args, RacNode node) {
//			this.types = types;
//			this.args = args;
//			this.node = node;
//		}
//	}

	/** Returns the receiver for executing the given expression,
	 * <code>expr</code> using a dynamic call. The argument is
	 * supposed to be either a non-static JClassFieldExpression
	 * referring to a model, ghost, spec_public, or spec_protected
	 * field or a non-static JMethodCallExpression calling a
	 * spec_public or spec_protected method. If the receiver is
	 * "this", a null value is returned; otherwise, the returned
	 * source code, if executed, evaluates the receiver and assign it
	 * to the fresh variable whose name is given by the name field of
	 * RacNode.
	 *
	 * <pre><jml>
	 * requires expr != null && expr instanceof JMethodCallExpression &&
	 *   expr instanceof JClassFieldExpression;
	 * </jml></pre>
	 */
	private RacNode receiverForDynamicCall(/*@ non_null @*/ JExpression expr) {
		JExpression prefix = (expr instanceof JMethodCallExpression) ?
				((JMethodCallExpression)expr).prefix() :
					((JClassFieldExpression)expr).prefix();

				// JLS 15.11
				// FieldAccess:
				//   Primary . Identifier
				//   super . Identifier
				//   ClassName . super . Identifier
				//
				// JLS 18.8 
				// Primary:
				//   PrimaryNoNewArray
				//   ArrayCreationExpression
				// PrimaryNoNewArray:
				//   Literal
				//   Type . class 
				//   void . class 
				//   this
				//   ClassName.this
				//   ( Expression )
				//   ClassInstanceCreationExpression
				//   FieldAccess
				//   MethodInvocation
				//   ArrayAccess

				// translate prefix if necessary. As the type checker adds
				// "this" for null prefix, it is not null after typechecking.
				// In addition, both "T.super" and "T.this" are not possible
				// because we are not translating inner classes yet.

				if (prefix instanceof JSuperExpression ||   // super or T.super
						prefix instanceof JThisExpression ||    // this or T.this
						prefix instanceof JTypeNameExpression) {// T
					return null; // should be interpreted as "this" by the caller
				} else {
					String var = varGen.freshVar();
					CType type = prefix.getApparentType();
					RacNode receiver = RacParser.parseStatement(
							toString(type) + " " + var + " = " + 
							defaultValue(type) + ";\n" +
							"$0\n",
							translate(prefix, var));
					receiver.setName(var);
					return receiver;
				}        
	}

	/**
	 * Translates a Java type name expression
	 */
	public void visitTypeNameExpression( JTypeNameExpression self ) {
		// CType type = self.getApparentType();
	}

	/**
	 * Translates a Java this expression. The translation rule for 
	 * "this" expression is defined as:
	 *
	 * <pre>
	 *   [[E.this, r]] = 
	 *      r = E.this;
	 * </pre>
	 *
	 * In an interface, however, "this" is translated into the private
	 * delegee field of the surrogate class.
	 */
	public void visitThisExpression( JThisExpression self ) 
	{
		//Debug.msg("In JThisExpression");

		JExpression prefix = self.prefix();
		RacNode result = null;
		if (prefix == null) {
			// In interface "this" is translated into the delegee
			// field of the surrogate class.
			String delegee = "this";
			if (TransType.genSpecTestFile) {
				delegee = "this.delegee_" + TransType.ident() + "()";
			}
			if (TransType.isInterface()) {
				delegee = "((" + TransType.ident() + ") " 
				+ VN_DELEGEE + ")";
			}
			result = RacParser.parseStatement(GET_ARGUMENT() + " = " + 
					delegee + ";");

			// adds "this" to diagnostic terms, i.e., the set of
			// variables whose values are to be printed if the assertion
			// is violated.
			addDiagTermThis();

		} else {
			result = RacParser.parseStatement(
					GET_ARGUMENT() + " = $0.this;", prefix);
		}
		RETURN_RESULT(result);
	}

	/**
	 * Translates a Java super expression. The translation rules for this 
	 * expression is defined as follows.
	 *
	 * <pre>
	 *   [[super, r]] = 
	 *      r = super;
	 * </pre>
	 */
	public void visitSuperExpression( JSuperExpression self ) {
		//Debug.msg("In JSuperExpression");

		RacNode n = RacParser.parseStatement(GET_ARGUMENT() + " = super;");
		RETURN_RESULT(n);
	}

	/**
	 * Translates a Java class expression. The translation rules for
	 * this expression is defined as follows.
	 *
	 * <pre>
	 *   [[T.class, r]] = 
	 *      r = T.class;
	 * </pre>
	 */
	public void visitClassExpression( JClassExpression self ) 
	{
		//Debug.msg("In ClassExpression");

		RacNode result = RacParser.parseStatement(
				GET_ARGUMENT() + " = " + self.prefixType() + ".class;");
		RETURN_RESULT(result);
	}

	/**
	 * Translates an explicit constructor invocation
	 */
	public void visitExplicitConstructorInvocation(
			JExplicitConstructorInvocation self)
	{
		//Debug.msg("In ExplicitConstructorInvocation");

		fail("Explicit constructor invocation not allowed in assertions!");
	}

	/**
	 * Translates a Java array length expression. The translation
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[E.length, r]] = 
	 *      T_E v = d_T_E;
	 *      [[E, v]]
	 *      r = v.length;
	 * </pre>
	 */
	public void visitArrayLengthExpression( JArrayLengthExpression self ) 
	{
		//Debug.msg("In ArrayLengthExpression");

		CType type = self.prefix().getApparentType();
		String v = freshVar();
		RacNode n = translate(self.prefix(), v);
		n = RacParser.parseStatement(
				toString(type) + " " + v + " = " + defaultValue(type) + ";\n" +
				"$0\n" +
				GET_ARGUMENT() + " = " + v + ".length;", n);
		RETURN_RESULT(n);
	}

	/**
	 * Translates a Java array access expression. The translation
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[E1[E2], r]] = 
	 *      T_E1 v1 = d_T_E1;
	 *      T_E2 v2 = d_T_E2;
	 *      [[E1, v1]]
	 *      [[E2, v2]]
	 *      r = v1[v2];
	 * </pre>
	 */
	public void visitArrayAccessExpression( JArrayAccessExpression self ) 
	{
		//Debug.msg("In ArrayAccessExpression");

		JExpression prefix = self.prefix();
		JExpression accessor = self.accessor();

		String demvar = freshVar(), angvar = freshVar();
		String v1 = freshVar();
		RacNode n1 = translate(prefix, v1, demvar, angvar);
		String v2 = freshVar();
		RacNode n2 = translate(accessor, v2, demvar, angvar);
		String[] strArrayAssertion = 
			TransUtils.createBigintConvertionAssertion(accessor.getApparentType(),
					CStdType.Integer);
		n1 = RacParser.parseStatement(
				"boolean " + demvar + " = false, " + angvar + " = false;\n" +
				toString(prefix.getApparentType()) + " " + v1 + 
				" = " + defaultValue(prefix.getApparentType()) + ";\n" +
				toString(accessor.getApparentType()) + " " + v2 + 
				" = " + defaultValue(accessor.getApparentType()) + ";\n" +
				"$0\n" +
				"if (!" + demvar + ") {\n" +
				"$1\n" +
				"}",
				n1, n2.incrIndent());

		String resvar = GET_ARGUMENT();
		String body = strArrayAssertion[0] + 
		((accessor.getApparentType() == JmlStdType.Bigint) ? v2 : "") +
		strArrayAssertion[1] + resvar + " = " + 
		v1 + "[" + applyArrayAccessExpression(v2, accessor.getApparentType(),
				CStdType.Integer) + "];";

				if (self.getApparentType() == CStdType.Boolean) {
					n1 = wrapBooleanResult(n1, body, resvar, demvar, angvar);
				} else {
					n1 = RacParser.parseStatement(
							"$0\n" +
							"if (" +demvar+ ") { throw JMLChecker.DEMONIC_EXCEPTION; }\n" +
							"if (" +angvar+ ") { throw JMLChecker.ANGELIC_EXCEPTION; }\n" +
							body, n1);
				}
				RETURN_RESULT(n1);
	}

	//translate array accessor from \bigint to numerical type is necessary
	public String applyArrayAccessExpression(String strVar, CType typeAccessor, CType typeNumber )
	{
		String strRet;

		String[] strArray = TransUtils.applyBigintToNumber(typeAccessor, typeNumber);
		strRet = strArray[0] + strVar + strArray[1];

		return strRet;   
	}

	/**
	 * Translates a Java name expression. The translation rules for this 
	 * expression is defined as follows.
	 *
	 * <pre>
	 *   [[n, r]] = 
	 *      r = n;
	 * </pre>
	 */
	public void visitNameExpression( JNameExpression self ) 
	{
		//Debug.msg("In NameExpression");

		RacNode stmt = RacParser.parseStatement(
				GET_ARGUMENT() + " = " + self.getName() + ";");
		RETURN_RESULT(stmt);
	}


	/**
	 * Translates a Java local variable expression. The translation
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[x, r]] = 
	 *      r = x;
	 * </pre>
	 */
	public void visitLocalVariableExpression( JLocalVariableExpression self ) 
	{
		//Debug.msg("In LocalVariableExpression");
		String resultVar = (String) paramStack.pop();
		RacNode stmt = RacParser.parseStatement(
				resultVar + " = " + transLocalVariable(self) + ";");
		resultStack.push(stmt);
	}

	private String transLocalVariable(JLocalVariableExpression self) {
		String ident = self.ident();

		// If exists, use generated RAC field for JML variables such
		// as old variables (see TransMethod.translateLetVarDecl())
		if (self.variable() instanceof JmlVariableDefinition) {
			JmlVariableDefinition var = 
				(JmlVariableDefinition) self.variable();
			if (var.hasRacField()) {
//				CType type = var.getType();
				ident = TransUtils.unwrapObject(var.getType(),
						var.racField() + ".value()");

				// add to the set of variables whose values are
				// to be printed if the assertion is violated.
				addDiagTerm(var);
			}
		}

		// if this expression denotes a formal parameter, add the
		// formal parameter to the set of variables whose values are
		// to be printed if the assertion is violated.
		if (self.variable() instanceof JFormalParameter) {
			addDiagTerm((JFormalParameter)self.variable());
		}

		return ident;
	}

	/**
	 * Translates a Java parenthesized expression. The translation
	 * rules for this expression is defined as follows.
	 *
	 * <pre>
	 *   [[(E), r]] = [[E, r]]
	 * </pre>
	 */
	public void visitParenthesedExpression( JParenthesedExpression self ) 
	{
		//Debug.msg("In JParenthesedExpression");
		self.expr().accept(this);
	}

	/**
	 * Translates a Java object allocator expression. The general
	 * translation rule for the Java object allocator expression is
	 * defined as follow.
	 *
	 * <pre>
	 *   [[new T(E1, ..., En), r]] =
	 *     T_E1 v1 = d_T_E1;
	 *     ...
	 *     T_En vn = d_T_En;
	 *     [[E1, v1]]
	 *     ...
	 *     [[En, vn]]
	 *     r = new T(v1, ..., vn);
	 * </pre>
	 *
	 * If the referenced constructor is effectively model (including
	 * constructors declared in model types), there are three
	 * possibilities. If the constructor is not executable (i.e., has
	 * no body), then the expression is translated into an angelic
	 * undefinedness. Otherwise, the expression is translated into
	 * either a static or dynamic call to the model constructor. If
	 * the model constructor comes from the same class or interface
	 * where the assertion being translated in specified, then static
	 * call is used; otherwise, dynamic call is used.
	 *
	 * <p> A spec_public or spec_protected constructor is always
	 * executable, and is translated into either a dynamic or static
	 * call.
	 *
	 * @see TransType#dynamicCallNeeded(CClass)
	 * @see #nonExecutableExpression()
	 * @see #translateToStaticNewObjectExpression(JNewObjectExpression,boolean)
	 * @see #translateToDynamicNewObjectExpression(JNewObjectExpression,boolean)
	 * @see #visitMethodCallExpression(JMethodCallExpression)
	 */
	public void visitNewObjectExpression( JNewObjectExpression self ) 
	{
		//Debug.msg("In JNewObjectExpression");

		// handle model/spec_public/spec_protected constructors
		CMethod meth = self.constructor();
		if (meth instanceof JmlSourceMethod) {
			JmlSourceMethod cmeth = (JmlSourceMethod) meth;
			if (cmeth.isEffectivelyModel()) {
				if (cmeth.isExecutableModel()) {
//					if (TransUtils.useReflection() // no -F option?
//					&& TransType.dynamicCallNeeded(meth.owner())) {
//					translateToDynamicNewObjectExpression(self, false);
//					} else {
					translateToStaticNewObjectExpression(self, false);
					// }
				} else {
					// non-executable model method
					warn(self.getTokenReference(), 
							RacMessages.NOT_EXECUTABLE,
							"A call to model constructor \"" +
							cmeth.ident() + "\"");

					nonExecutableExpression();
				} 
				return;
			} else if (cmeth.isSpecPublic() || cmeth.isSpecProtected()) {
//				if (TransUtils.useReflection() // no -F option?
//				&& TransType.dynamicCallNeeded(meth.owner())) {
//				translateToDynamicNewObjectExpression(self, true);
//				} else {
				translateToStaticNewObjectExpression(self, true);
//				}
				return;
			}
		}

		translateToStaticNewObjectExpression(self, false);
	}

	/**
	 * Translates the given new object expression into a static call.
	 * If the argument, <code>isSpecPublic</code>, is false, the
	 * translated code has the form:
	 *
	 * <pre>
	 *  T1 v1 = E1; ...; Tn vn = En; 
	 *  result = new T(v1, ..., vn); 
	 *  </pre>
	 *
	 * Otherwise, the translated code has the following form:
	 *
	 * <pre>
	 *  T1 v1 = E1; ...; Tn vn = En; 
	 *  result = MN_SPEC_PUBLIC$T(v1, ..., vn); 
	 *  </pre>
	 */
	private void translateToStaticNewObjectExpression(
			/*@ non_null @*/ JNewObjectExpression self,
			boolean isSpecPublic) {

		// code for evaluating arguments. 
		// args.str has the form: "(v1, v2, ..., vn)"
		// args.node has the form: T1 v1 = E1; ...; Tn vn = En; 
		// code for evaluating arguments
		StringAndNodePair args = argumentsForStaticCall(
				self.params(), null, null);

		// method name to call, either factory or new expression
		CType type = self.getApparentType();
		String meth = isSpecPublic ?
				// static factory method
				type + "." + TransUtils.specPublicAccessorName(MN_INIT) :
					// new expression
					"new " + type;

				// code for method call
				RacNode result = RacParser.parseStatement(
						GET_ARGUMENT() + " = " + meth + args.str + ";");
				if (args.node != null)
					result = RacParser.parseStatement("$0\n$1", args.node, result);

				RETURN_RESULT(result);
	}

	/** Translates the given model, spec_public, or spec_protected
	 * constructor call expression, <code>expr</code>, which was
	 * determined to be executed using a dynamic call. If the
	 * argument, <code>isSpecPublic</code>, is true, the new
	 * expression is for a spec_public or spec_protected constructor;
	 * otherwise, it is for a model constructor. 
	 */
//	private void translateToDynamicNewObjectExpression(
//			/*@ non_null @*/ JNewObjectExpression expr,
//			boolean isSpecPublic) {
//		needDynamicInvocationMethod();
//
//		String receiver = "null"; // null for static method call
//
//		// generate code for evaluating arguments; 
//		// args.node has the form: T1 v1 = E1; ...; Tn vn = En; 
//		// args.types has the form: "new Class[] { T1, ..., Tn }" and 
//		// args.args has the form: "new Object[] { v1, ..., vn }".
//		DynamicCallArg args = argumentsForDynamicCall(
//				expr.params(), expr.constructor().parameters());
//		RacNode argEval = args.node;
//		String types = args.types;
//		String args2 = args.args;
//
//		// target class of dynamic call
//		CClass clazz = ((CClassType) expr.getType()).getCClass();
//		// cn, fully qualified name of the target class
//		String cn = TransUtils.dynamicCallName(clazz);
//		// mn, the name of spec_public accessor method
//		String mn = isSpecPublic ?
//				"\"" +TransUtils.specPublicAccessorName(MN_INIT) +"\"" : null;
//
//				// return code for dyanmic call to the acessor
//				String tvar = varGen.freshVar(); // for type args to the call
//				String avar = varGen.freshVar(); // for value args to the call
//				String var = varGen.freshVar();  // for holding result of the call
//				String resultVar = GET_ARGUMENT();
//				RacNode result = RacParser.parseStatement(
//						(argEval == null ? "" : "$0\n") +
//						"java.lang.Class[] " + tvar + " = " + types + ";\n" +
//						"java.lang.Object[] " + avar + " = " + args2 + ";\n" +
//						"java.lang.Object " + var + " = rac$invoke(\"" + cn + "\", " + 
//						receiver+ ", " + mn + ", " + tvar + ", " + avar + ");\n" +
//						resultVar + " = " + 
//						TransUtils.unwrapObject(expr.getApparentType(), var) + ";",
//						argEval);
//				RETURN_RESULT(result);
//	}

	/**
	 * Translates an object allocator expression for an anonymous class.
	 */
	public void visitNewAnonymousClassExpression( 
			JNewAnonymousClassExpression self ) 
	{
		// !FIXME! translate self? oh, no...
		RacNode result = RacParser.parseStatement(
				GET_ARGUMENT() + " = $0;", self);
		RETURN_RESULT(result);
	}

	/**
	 * Translates an array allocator expression.
	 */
	public void visitNewArrayExpression( JNewArrayExpression self ) 
	{
		// !FIXME! translate self, i.e., dims and initializer
		RacNode result = RacParser.parseStatement(
				GET_ARGUMENT() + " = $0;", self);
		RETURN_RESULT(result);
	}

	public void visitArrayDimsAndInit( JArrayDimsAndInits self ) {
		// !FIXME! array dimension and init
	}

	public void visitArrayInitializer( JArrayInitializer self ) {
		// !FIXME! array initializer
	}

	/**
	 * Translates a Java field expression. The translation rules for
	 * this expression is defined as follows.
	 *
	 * <pre>
	 *   [[E.x, r]] = 
	 *     T_E v = d_T_E;
	 *     [[E, v]]
	 *     r = v;
	 * </pre>
	 *
	 * If the referenced field is a model field, generates a model
	 * method call instead.
	 *
	 * @see #transPrefix
	 */
	public void visitFieldExpression( JClassFieldExpression self ) {
		JExpression prefix = self.prefix();

		// add "this" to the set of diagnostic terms for composing
		// an assertion violation message if necessary.
		if ((prefix instanceof JThisExpression) ||
				(prefix instanceof JSuperExpression)) {
			addDiagTermThis();
		}

		// not executable, e.g., fields of model class or interface?
		if (isNonExecutableFieldReference(self)) {

			warn(self.getTokenReference(), 
					RacMessages.NOT_EXECUTABLE,
					"A reference to field \"" + self.ident() + "\"");

			translateNonExecutableFieldExpression(self);
			return;
		}

		String ident = self.ident();
		RacNode result = null;

		// generated fields?
		final String var = GET_ARGUMENT();
		if (ident.equals(JAV_OUTER_THIS)) {
			result = RacParser.parseStatement(
					var + " = " + 
					prefix.getApparentType().getCClass().owner().getType() + 
			".this;");
			RETURN_RESULT(result);
		}

		int index = ident.indexOf("_$");
		if (index != -1) { // local var?
			result = RacParser.parseStatement(
					var + " = " + ident.substring(0, index) + ";");
		} else {
			long mods = ((CField)self.getField()).modifiers();
			if (specAccessorNeeded(mods)) {
				// if spec_public (or spec_proteced), generate code for 
				// dynamic call to the corr. accessor method.
				result = transFieldReference(self, var, MN_SPEC);
			} else {
				// if model variable, convert this to accessor method call
				// and record this fact by adding the field to modelFieldRefs.
				if (hasFlag(mods, ACC_MODEL)) {
					result = transFieldReference(self, var, MN_MODEL);
				} else if (hasFlag(mods, ACC_GHOST)) {
					result = transFieldReference(self, var, MN_GHOST);
				} else if (TransType.genSpecTestFile && !hasFlag(mods,ACC_PUBLIC)) {
					// FIXME ??? Use transReference?
					String id = "prot$" + ident + "$" + typeDecl.ident() + "()";
					result = transPrefixSpec(prefix, var + " = $0." + id + ";",false);

					// add self to the set of diagnostic terms for composing
					// an assertion violation message if necessary.
					if (prefix instanceof JThisExpression || prefix == null) {
						addDiagTerm(self.ident());
					}
				} else {
					result = transPrefix(prefix, var + " = $0." + ident + ";");

					// add self to the set of diagnostic terms for composing
					// an assertion violation message if necessary.
					if (prefix instanceof JThisExpression || prefix == null) {
						addDiagTerm(self.ident());
					}
				}
			}

			// guard against undefinedness if boolean type
			if (self.getApparentType().isBoolean()) {
				result = guardUndefined(context, result, var);
			}
		}
		RETURN_RESULT(result);
	}

	/**
	 * Returns true if the referenced field (by the argument
	 * expression) is not executable. If the referenced field is
	 * declared inside a model class or interface, it is not
	 * executable.  A model/ghost field declared in a non-model
	 * class/interface is executable, e.g., by calling its access
	 * method.
	 */
	protected boolean isNonExecutableFieldReference(JClassFieldExpression expr)
	{
		CFieldAccessor field = expr.getField();
		if (field instanceof JmlSourceField) {
			JmlSourceField sfield = (JmlSourceField) field;
			return ((JmlSourceClass)sfield.owner()).isEffectivelyModel();
		}
		return false;
	}

	/** Translates the given field expression that is determined to be
	 * non-executable. */
	private void translateNonExecutableFieldExpression( 
			JClassFieldExpression expr) {
		if (context.enabled() && expr.getApparentType().isBoolean()) {
			String var = GET_ARGUMENT();
			RacNode result = RacParser.parseStatement(
					"// from non-executable field reference\n" +
					context.angelicValue(var) + ";\n");
			RETURN_RESULT(result);
		} else {
			nonExecutableExpression();
		}
	}

	/**
	 * Translates a class field expression that references a model,
	 * ghost, spec_public, or spec_protected field. The translated
	 * code dynamically invokes the corresponding accessor method. The
	 * translation rules is defined as follows.
	 *
	 * <pre>
	 * [[e.x, r]] ==
	 *  T_e v = init_T_e;
	 *  [[e, v]]
	 *  Object o = rac$invoke(C, v, x$C, null, null);
	 *  if (o == null) {
	 *     throw new JMLNonExecutableException();
	 *  }
	 *  r = (T)o;
	 * </pre>
	 * where <code>C</code> is the name of class where <code>x</code> is 
	 * declared and <code>T</code> is the type of <code>x</code>.
	 *
	 * <pre><jml>
	 * requires self != null && resultVar != null;
	 * </jml></pre>
	 */

	private RacNode transFieldReference(JClassFieldExpression self,
			String resultVar, String accPrefix) {
		// owner of the referrenced field
		CClass cls = self.getField().owner();

		// no attempt for inheritance, e.g., from JDK classes.
		if (TransUtils.excludedFromInheritance(cls)) {
			warn(self.getTokenReference(), 
					RacMessages.NOT_EXECUTABLE,
					"A reference to field \"" + self.ident() + "\"");

			paramStack.push(resultVar);
			translateNonExecutableFieldExpression(self);
			return (RacNode) resultStack.pop();
		}

		// decide the receiver of dynamic call (model field access method)
		RacNode receiverNode = null;
		String receiver = "";
		if (isStatic(self)) {
			receiver = "null"; // null for static field
		} else if (TransType.genSpecTestFile && hasFlag(self.getField().getField().modifiers(),ACC_PROTECTED)) {
			receiverNode = receiverForDynamicCall(self);
			receiver = (receiverNode != null) ? receiverNode.name() :"this";
			accPrefix = "prot$";
		} else {
			receiverNode = receiverForDynamicCall(self);
			receiver = (receiverNode != null) ? receiverNode.name() : 
				(TransType.genSpecTestFile &&  (!accPrefix.equals("model$") && !accPrefix.equals("ghost$"))) ? 
						"this.delegee_" + typeDecl.ident() + "()"
						: "this";
		}

		// cn, fully qualified name of the target class
		String cn = TransUtils.dynamicCallName(cls);
		// mn, the name of model/ghost/spec_public accessor method
		String mn = accPrefix + self.ident() + "$" + cls.ident();

		// if possible, return code for static method call
		if (canMakeStaticCall(self, receiver)) {
			if (isStatic(self)) {
				receiver = cn;
			} else {
				if (cls.isInterface()) {
					receiver = "((" +cn+ ") " + 
							"JMLChecker.getSurrogate(\"" +cn+ 
							"\", rac$forName(\"" +cn+ "\"), " +receiver+ "))";
				}
			}
			return RacParser.parseStatement(
					(receiverNode == null ? "" : "$0\n") + // prefix eval code
					resultVar + " = " + receiver + "." + mn + "();",
					receiverNode);
		}

		// record that a model field inheritance mechanism is needed
		needDynamicInvocationMethod();

		// return code for dyanmic call to the accessor
		String var = varGen.freshVar(); // to hold the result of dcall
		return RacParser.parseStatement(
				(receiverNode == null ? "" : "$0\n") + // prefix eval code
				"java.lang.Object " + var + " = rac$invoke(\"" + cn + "\", " + 
				receiver + ", \"" + mn + "\", null, null);\n" +
				resultVar + " = " + 
				TransUtils.unwrapObject(self.getApparentType(),var) + ";",
				receiverNode);
	}

	/** Returns true if a static (non-dynamic) call can be made to the
	 * given field expression, <code>expr</code>. The given expression
	 * is assumed to be a reference to a model, ghost, spec_public, or
	 * spec_protected field. */
	public static boolean canMakeStaticCall(JClassFieldExpression expr,
			String receiver) {
//		if (!TransUtils.useReflection())
//		return true;

//		CClass clazz = expr.getField().owner();

		// must be in the same type currently being translated
//		if (TransType.dynamicCallNeeded(clazz))
//		return false;

		// static field can be always called statically
		if (isStatic(expr))
			return true;

		// non-static class fields can always be called statically
		if (!TransType.isInterface())
			return true;

		// non-static interface fields of current object (this) is okay.
		if (receiver.equals("this") || receiver.startsWith("this.delegee"))
			return true;

		return false;
	}

	/** Returns true if the given field expression refers to a static
	 * field. */
	private static boolean isStatic(JClassFieldExpression expr) {
		return hasFlag(((CField)expr.getField()).modifiers(), ACC_STATIC);
	}

	/** Returns true if the given method call expression refers to a
	 * static method. */
//	private static boolean isStatic(JMethodCallExpression expr) {
//		return hasFlag(expr.method().modifiers(), ACC_STATIC);
//	}

	// ----------------------------------------------------------------------
	// LITERALS
	// ----------------------------------------------------------------------

	/**
	 * Translates a boolean literal.
	 */
	public void visitBooleanLiteral( JBooleanLiteral self ) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + self.booleanValue() + ";"));
	}

	/**
	 * Translates a character literal.
	 */
	public void visitCharLiteral( JCharLiteral self ) {
		Character chValue = (Character) self.getValue();
		char value;
		if( chValue != null) {
			value = chValue.charValue();
		} else {
			value = self.image().charAt(0); // !!! false
		}
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = '" + TransUtils.toPrintableString(value) +
		"';"));
	}

	/**
	 * Translates an ordinal literal.
	 */
	public void visitOrdinalLiteral( JOrdinalLiteral self ) {
		Number value = self.numberValue();
		CType type = self.getApparentType();

		if (type == CStdType.Byte) {
			visitByteLiteral(value.byteValue());
		} else if (type == CStdType.Integer) {
			visitIntLiteral(value.intValue());
		} else if (type == CStdType.Long) {
			visitLongLiteral(value.longValue());
		} else if (type == CStdType.Short) {
			visitShortLiteral(value.shortValue());
		} else if (type == JmlStdType.Bigint) {
			visitBigintLiteral(value.longValue()); // !FIXME! ? will this do?
		} else {
			fail();
		}
	}

	/**
	 * Translates a byte literal.
	 */
	protected void visitByteLiteral( byte value ) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + "(byte)" + value + ";"));
	}

	/**
	 * Translates a int literal.
	 */
	protected void visitIntLiteral(int value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + value + ";"));
	}

	/**
	 * Translates a long literal.
	 */
	protected void visitLongLiteral(long value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + value + "L;"));
	}

	/**
	 * Translates a \bigint literal.
	 */
	protected void visitBigintLiteral(long value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = java.math.BigInteger.valueOf(" + value + "L);"));
	}

	/**
	 * Translates a short literal.
	 */
	protected void visitShortLiteral(short value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + "(short)"+ value + ";"));
	}

	/**
	 * Translates a real literal.
	 */
	public void visitRealLiteral( JRealLiteral self ) {
		Number value = self.numberValue();
		CType type = self.getApparentType();
		assertTrue(value != null);

		if( type == CStdType.Double) {
			visitDoubleLiteral(value.doubleValue());
		} else if( type == CStdType.Float) {
			visitFloatLiteral(value.floatValue());
		} else if( type == JmlStdType.Real ) {
			visitDoubleLiteral(value.doubleValue()); // !FIXME! ? will this do?
		} else {
			fail();
		}
	}

	/**
	 * Translates a double literal.
	 */
	protected void visitDoubleLiteral(double value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + TransUtils.toString(value) + ";"));
	}

	/**
	 * Translates a float literal.
	 */
	protected void visitFloatLiteral(float value) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + TransUtils.toString(value) + ";"));
	}

	/**
	 * Translates a string literal. 
	 */
	public void visitStringLiteral( JStringLiteral self) {
		// !FIXME! unicode handling
		String value = self.stringValue();
		StringBuffer s = new StringBuffer();
		for (int i = 0; i < value.length(); i++) {
			char c = value.charAt(i);
			switch (c) {
			case '\n' : s.append("\\n"); break;
			case '\r' : s.append("\\r"); break;
			case '\t' : s.append("\\t"); break;
			case '\b' : s.append("\\b"); break;
			case '\f' : s.append("\\f"); break;
			case '\"' : s.append("\\\""); break;
			case '\'' : s.append("\\\'"); break;
			case '\\' : s.append("\\\\"); break;
			default:
				s.append(c);
			}
		}
		value = s.toString();

		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = " + '"' + value + '"' + ";"));
	}

	/**
	 * Translates a null literal.
	 */
	public void visitNullLiteral( JNullLiteral self ) {
		RETURN_RESULT(RacParser.parseStatement(
				GET_ARGUMENT() + " = null;"));
	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/** Translates a non-executable non-boolean expression. The
	 * expression is translated into the Java statement of the form:
	 * <code>throw new JMLNonExectutableException();</code>. The
	 * result variable is popped from the parameter stack and the
	 * generated <code>RacNode</code> object is pushed ont the result
	 * stack. */
	//@ assignable resultStack;
	protected void nonExecutableExpression() {
//		String var = GET_ARGUMENT(); // consume argument
		RacNode result = RacParser.parseStatement(
				"if (true) {\n" + // this prevents potential "reachability error"
				"  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
		"}");
		RETURN_RESULT(result);
	}

	/** Translates a non-executable boolean expression. The expression
	 * is translated into either <code>true</code> or
	 * <code>false</code> depending on the current polarity of
	 * translation. The result variable is popped from the parameter
	 * stack and the generated <code>RacNode</code> object is pushed
	 * ont the result stack. */
	protected void booleanNonExecutableExpression() {
		if (context.enabled()) {
			RETURN_RESULT(RacParser.parseStatement(
					"// from a non_executable, boolean, JML clause\n" +
					context.angelicValue(GET_ARGUMENT()) + ";"));
		} else {
			nonExecutableExpression();
		}
	}

	/** Records that we need to generate the dynamic invocation
	 * method. E.g., to evaluate model, ghost, spec_public, or
	 * spec_protected fields or spec_public or spec_protected methods. */
	private void needDynamicInvocationMethod() {
		TransType.dynamicInvocationMethodNeeded = true;
	}

	/** Returns true if the modifiers indicate that we need to generate 
	 * specification-only accessor method.   The argument modifier is 
	 * typically from a model field declaration.     
	 *
	 * <pre><jml>
	 * ensures \result == (hasFlag(modifiers, ACC_PRIVATE) &&
	 *	    (hasFlag(modifiers, ACC_SPEC_PUBLIC) ||
	 *	     hasFlag(modifiers, ACC_SPEC_PROTECTED)));
	 * </jml></pre>
	 */
	public static boolean specAccessorNeeded(long modifiers) {
		return //hasFlag(modifiers, ACC_PRIVATE) &&
		(hasFlag(modifiers, ACC_SPEC_PUBLIC) ||
				hasFlag(modifiers, ACC_SPEC_PROTECTED));
	}

	/** Translates an AST into Java statements. */
	protected RacNode translate(JPhylum node, String var)
	{
		//Debug.msg("In translate: " + node.getClass().getName() + " " + node);
		paramStack.push(var);
		node.accept(this);
		//Debug.msg("   stack size before return pop: " + resultStack.size());
		return (RacNode) resultStack.pop();
	}

	/** Translates an AST into Java statements. */
	protected RacNode translate(JPhylum node, 
			String resvar,
			String demvar,
			String angvar)
	{
		paramStack.push(resvar);
		node.accept(this);
		RacNode stmt = (RacNode) resultStack.pop();

		if (demvar == null) {
			return stmt;
		}

		return RacParser.parseStatement(
				"try {\n" +
					"$0\n" +
					"}\n" +
					"catch (JMLNonExecutableException jml$e0) {\n" +
					"  " + angvar + " = true;\n" +
					"}\n" +
					"catch (java.lang.Exception jml$e0) {\n" +
					"  " + demvar + " = true;\n" +
					"}", stmt.incrIndent());	
	}

	/** Returns a new <code>RacNode</code> that wraps the given
	 * statement, <code>stmt</code>, inside a try-catch statement to
	 * guard against undefinedness caused by runtime exceptions and
	 * non-executable expression. The statement is supposed to store
	 * some value to the variable named <code>var</code>. */
	protected RacNode guardUndefined(RacContext ctx, RacNode stmt, String var)
	{
		// is contextual interpretation disabled?
		if (!ctx.enabled()) {
			return stmt;
		}

		return RacParser.parseStatement(
				"try {\n" +
				"$0\n" +
				"}\n" +
				"catch (JMLNonExecutableException jml$e0) {\n" +
				"  " + ctx.angelicValue(var) + ";\n" +
				"}\n" +
				"catch (java.lang.Exception jml$e0) {\n" +
				"  " + ctx.demonicValue(var) + ";\n" +
				"}", stmt.incrIndent());	
	}


	/** Returns the default value of the type <code>type</code>. */
	public static String defaultValue(CType type) {
		if (type instanceof CNumericType) {
			return (type == JmlStdType.Bigint) ?
					"java.math.BigInteger.ZERO" : "0";
		} else if (type.isBoolean()) {
			return "false";
		} else
			return "null";
	}

	/**
	 * Returns the string representation of the given type. If the
	 * type is <code>JmlStdType.TYPE</code>, the result is 
	 * <code>"java.lang.Class"</code>; otherwise it is 
	 * <code>value.toString()</code>.
	 *
	 * @see TransUtils#toString(CType)
	 */    
	protected String toString(CType type) {
		return TransUtils.toString(type);
	}

	/** Returns a fresh variable name. */
	protected String freshVar() {
		return varGen.freshVar();
	}

	/** Returns the top element of the parameter stack. */
	protected String GET_ARGUMENT() 
	{
		return (String) paramStack.pop();
	}

	/** Peeks the top element of the parameter stack. */
	protected String PEEK_ARGUMENT() 
	{
		return (String) paramStack.peek();
	}

	/** Puts the given object to the parameter stack. */
	public void PUT_ARGUMENT(Object obj) {
		paramStack.push(obj);
	}

	/** Returns the top element of the result stack. */
	public Object GET_RESULT() {
		return resultStack.pop();
	}

	/** Puts the given object to the result stack. I.e., simulates
	 * returning of visitor method calls (to the calling visitor
	 * method).
	 */
	//@ assignable resultStack;
	protected void RETURN_RESULT(Object obj) {
		resultStack.push(obj);
	}

	/**
	 * Produce a warning message with the given token reference,
	 * message description, and argument to message description. */
	public static void warn(TokenReference tref, 
			MessageDescription description,
			Object obj) {
		JmlRacGenerator.warn(tref, description, obj);
	}

	// ----------------------------------------------------------------------
	// MANIPULATION OF DIAGNOSTIC TERMS
	// ----------------------------------------------------------------------

	/**
	 * Initializes the set of terms to be printed when the assertion
	 * is violated. This set is called <em>diagnostic terms</em>.
	 */
	protected void initDiagTerms() {
		diagTerms.clear();
	}

	/**
	 * Adds the given term to the set of terms to be printed when the
	 * assertion is violated.
	 */    
	protected void addDiagTerm(/*@ non_null @*/ Object term) {
		diagTerms.add(term);
	}

	/**
	 * Adds "this" to the set of terms to be printed when the
	 * assertion is violated.
	 */    
	protected void addDiagTermThis() {
		diagTerms.add(DT_THIS);
	}

	/**
	 * Adds "\result" to the set of terms to be printed when the
	 * assertion is violated.
	 */    
	protected void addDiagTermResult() {
		diagTerms.add(DT_RESULT);
	}

	/**
	 * Returns true if there is any diagnostic terms accumulated.
	 */   
	protected boolean hasDiagTerms() {
		return !diagTerms.isEmpty();
	}

	/**
	 * Returns a string representation of Java statements that, if
	 * executed, prints the values of diagnostic terms accumulated so
	 * far and stores them to the given variable,
	 * <code>var</code>. The returned statements also declares the
	 * variable <code>var</code>.  If there is no diagnostic terms
	 * accumulated so far, then an empty string is returned.
	 */
	protected String diagTerms(/*@ non_null @*/ String var) {
		if (diagTerms.isEmpty()) {
			return "";
		}

		// save old check level
		String level = varGen.freshVar();
		String result = "  int " + level + " = JMLChecker.getLevel();\n";
		result += "  JMLChecker.setLevel(JMLChecker.NONE);\n";

		result += "  java.lang.String " + var + " = \"\";\n";
		boolean hasResult = false;
		boolean hasThis = false;
		for (Iterator i = diagTerms.iterator(); i.hasNext(); ) {
			Object term = i.next();
			if (term instanceof String) {
				// non-static field reference
				String fieldAccessor;

				if(JmlRacGenerator.checking_mode == JmlRacGenerator.WRAPPER) {
					fieldAccessor =  "_chx_get_" + term + "()";
				} else {
					fieldAccessor = (String) term;
				}

				result += "  " +  var + " += \"\\n\\t"
				+ "'" + term + "' is \" + JMLChecker.toString(" 
				+ fieldAccessor + ");\n";
			} else if (term instanceof JFormalParameter) {
				String ident = ((JFormalParameter) term).ident();
				result += "  " + var + " += \"\\n\\t'" + ident 
				+ "' is \" + JMLChecker.toString(" + ident + ");\n";
			} else if (term instanceof JmlVariableDefinition) {
				String ident = ((JmlVariableDefinition) term).ident();
				String field = ((JmlVariableDefinition) term).racField();
				result += "  " + var + " += \"\\n\\t'" + ident 
				+ "' is \" + JMLChecker.toString(" + field + ");\n";
			} else if (term instanceof DiagTerm) {
				String expr = ((DiagTerm) term).term();
				Object val = ((DiagTerm) term).value();
				result += "  " + var + " += \"\\n\\t'\"" + 
				" + JMLChecker.toString(\"" + expr + "\") + " +
				"\"' is \" + JMLChecker.toString(" + val + ");\n";
			} else if (term == DT_THIS) {
				hasThis = true;
			} else if (term == DT_RESULT) {
				hasResult = true;
			}
		}

		// print \result if necessary
		if (hasResult) {
			result += "  " +  var + " += \"\\n\\t"
			+ "'\\\\result' is \" + JMLChecker.toString(" 
			+ VN_RESULT + ");\n";
		}

		// print "this" if necessary
		if (hasThis) {
			result += "  " +  var + " += \"\\n\\t"
			+ "'this' is \" + JMLChecker.toString("
			+ (TransType.isInterface() ? VN_DELEGEE : 
				TransType.genSpecTestFile ? 
						"this.delegee_" + typeDecl.ident() + "()" 
						: "this") + ");\n";
		}

		// restore old check level
		result += "  JMLChecker.setLevel(" + level + ");\n";

		return result;
	}

	/**
	 * The set of diagnostic terms. I.e., terms to be printed when the
	 * assertion gets violated.
	 *
	 * <pre><jml>
	 * private invariant (\forall Object o; diagTerms.contains(o); 
	 *   (o instanceof JFormalParameter) || (o instanceof String) ||
	 *   (o instanceof JmlVariableDefinition) ||
	 *   o == DT_THIS || o == DT_RESULT);
	 * </jml></pre>
	 *
	 */
	private Set diagTerms = new HashSet();

	/** Special object to denote "this" in the set of diagnostic terms. */
	private static final Object DT_THIS = new Object();

	/** Special object to denote "\result" in the set of diagnostic terms. */
	private static final Object DT_RESULT = new Object();

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** Generator of unique variable names. */
	protected /*@ non_null @*/ VarGenerator varGen;

	/** Variable to hold the reslt of the target expression. */
	protected /*@ non_null @*/ String resultVar;

	/** Stack for passing parameters to visitor methods. */
	protected Stack paramStack;

	/** Stack for returning result from visitor methods. */
	protected Stack resultStack;

	/** Current translation context. */
	protected RacContext context;

	/** Expression to translate. */
	protected JExpression expression;

	/** The type declaration within which this expression resides (the
	 * type of 'this'). */
	protected JTypeDeclarationType typeDecl;

	/** Is the expression already translated? */
	/*@ spec_protected @*/ private boolean translated = false;

	// ----------------------------------------------------------------------
	// INNER CLASSES
	// ----------------------------------------------------------------------

	/**
	 * A class representing a term to be presented when an assertion
	 * is violated.
	 */
	public static class DiagTerm {
		public DiagTerm(/*@ non_null @*/ String term, 
				/*@ non_null @*/ Object value) {
			this.term = term;
			this.value = value;
		}

		public /*@ non_null @*/ String term() {
			return term;
		}

		public /*@ non_null @*/ Object value() {
			return value;
		}

		/** Does the argument equal to this object? */
		public boolean equals(/*@ nullable @*/ Object obj) {
			if (this == obj) {
				return true;
			} else if (obj == null || getClass() != obj.getClass()) {
				return false;
			}
			DiagTerm other = (DiagTerm) obj;
			return term.equals(other.term()) && value.equals(other.value());
		}

		public int hashCode() {
			return 37 * term.hashCode() + value.hashCode();
		}

		private /*@ non_null @*/ String term;
		private /*@ non_null @*/ Object value;
	}
}
