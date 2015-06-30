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
 * $Id: TransMethodBody.java,v 1.53 2007/06/30 02:32:39 chalin Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlAssertOrAssumeStatement;
import org.jmlspecs.checker.JmlAssertStatement;
import org.jmlspecs.checker.JmlAssumeStatement;
import org.jmlspecs.checker.JmlGuardedStatement;
import org.jmlspecs.checker.JmlInvariantStatement;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlNondetChoiceStatement;
import org.jmlspecs.checker.JmlNondetIfStatement;
import org.jmlspecs.checker.JmlSpecStatement;
import org.jmlspecs.checker.JmlStdType;
import org.jmlspecs.checker.JmlUnreachableStatement;
import org.multijava.mjc.CNumericType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JAssertStatement;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JBreakStatement;
import org.multijava.mjc.JCatchClause;
import org.multijava.mjc.JCompoundStatement;
import org.multijava.mjc.JConstructorBlock;
import org.multijava.mjc.JContinueStatement;
import org.multijava.mjc.JDoStatement;
import org.multijava.mjc.JEmptyStatement;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JExpressionListStatement;
import org.multijava.mjc.JExpressionStatement;
import org.multijava.mjc.JForStatement;
import org.multijava.mjc.JIfStatement;
import org.multijava.mjc.JLabeledStatement;
import org.multijava.mjc.JReturnStatement;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JSwitchGroup;
import org.multijava.mjc.JSwitchStatement;
import org.multijava.mjc.JSynchronizedStatement;
import org.multijava.mjc.JThrowStatement;
import org.multijava.mjc.JTryCatchStatement;
import org.multijava.mjc.JTryFinallyStatement;
import org.multijava.mjc.JTypeDeclarationStatement;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JVariableDeclarationStatement;
import org.multijava.mjc.JWhileStatement;

/**
 * A visitor class for translating JML specification statements in 
 * a method body into assertion check code. The translated assertion
 * check code is stored as a <code>RacNode</code> in the AST of the 
 * specification statement and is expected to be pretty-printed by
 * the class {@link RacPrettyPrinter}. Translated are such specification
 * statements as <code>assume</code>, <code>assert</code>, and
 * <code>unreachable</code> statements.
 *
 * <pre>
 *                 TransConstuctorBody  JConstructorBlock
 *                         |                   |
 *                         +                   +
 *                         v                   V
 * TransType &lt;&gt;----- TransMethodBody -----&gt; JBlock
 *                         |                   |
 *       setAssertionCode()|&lt;&lt;call&gt;&gt;           +
 *                         V                   V
 *                 JmlAssertStatement ----|&gt; JStatement
 *                         ^
 *          assertionCode()|&lt;&lt;call&gt;&gt;
 *                         |
 *                 RacPrettyPrinter
 * </pre>
 *
 * @see #translate()
 * @see #visitJmlAssumeStatement(JmlAssumeStatement)
 * @see #visitJmlAssertStatement(JmlAssertStatement)
 * @see #visitCompoundStatement(JStatement[])
 * @see #visitJmlUnreachableStatement(JmlUnreachableStatement)

 * @author Yoonsik Cheon
 * @version $Revision: 1.53 $
 */
public class TransMethodBody extends RacAbstractVisitor {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Construct an object of <code>TransMethodBody</code>.
	 *
	 * @param varGen variable name generator
	 * @param mdecl method body to be translated
	 */
	public TransMethodBody(/*@ non_null @*/ VarGenerator varGen,
			/*@ non_null @*/ JmlMethodDeclaration mdecl,
			/*@ non_null @*/ JTypeDeclarationType typeDecl) {
		this.varGen = varGen;
		this.methodDecl = mdecl;
		this.body = mdecl.body();
		this.typeDecl = typeDecl;
	}

	// ----------------------------------------------------------------------
	// TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Performs the translation of method body and returns the resulting
	 * method body, which may be modified during the translation.
	 * For specification statements such as assume, assert, and
	 * unreachable, the translation produces their assertion check code 
	 * (of type <code>RacNode</code>) and stores them into their ASTs.
	 *
	 * <pre><jml>
	 *  ensures \result != null;
	 * </jml></pre>
	 *
	 * @see #visitJmlAssumeStatement(JmlAssumeStatement)
	 * @see #visitJmlAssertStatement(JmlAssertStatement)
	 * @see #visitCompoundStatement(JStatement[])
	 * @see #visitJmlUnreachableStatement(JmlUnreachableStatement)
	 */
	public JBlock translate() {
		//@ assume body != null;
		body.accept(this);
		return body;
	}

	// ----------------------------------------------------------------------
	// VISITORS FOR JML STATEMENTS
	// ----------------------------------------------------------------------

	/** 
	 * Translates the given JML <code>assert</code> statement and
	 * stores the translated assertion check code into the AST node.
	 * An <code>assert_redundantly</code> statement is translated only
	 * if the command-line option <code>noredundancy</code> is turned
	 * off (which is the default). The translated assertion check code
	 * has the following form:
	 *
	 * <pre>
	 * [[assert E;]] ==
	 *   boolean v = false;
	 *   [[E, v]]
	 *   if (!v) {
	 *     throw new JMLAssertError();
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 * also
	 *   requires self != null;
	 *   modifies self.*;
	 *   ensures isCheckable(self) ==> self.assertionCode() != null;
	 * </jml></pre>
	 *
	 * @see #visitJmlAssumeStatement(JmlAssumeStatement)
	 * @see #translate()
	 */
	public void visitJmlAssertStatement(JmlAssertStatement self) {
		if (!isCheckable(self))
			return;
		//@ assume !self.isRedundantly() || !Main.racOptions.noredundancy();

		// translate predicate part
		RacContext ctx = RacContext.createPositive();
		RacPredicate pred = new RacPredicate(self.predicate());
		String v1 = varGen.freshVar();

		// FRioux - Experimental test for efficiency (begin)

		RacNode n1 = null;

//		if(!Main.aRacOptions.oldSemantics()){
			TransExpression2 transx = new TransExpression2(varGen, ctx, pred, v1, typeDecl, "JMLAssertError");
			n1 = transx.stmt(true).incrIndent();
//		}
//		else{
//			TransPredicate trans = new TransPredicate(varGen, ctx, pred, v1, typeDecl);
//			n1 = trans.wrappedStmt().incrIndent();
//		}

		// FRioux - Experimental test for efficiency (end)

		String msg = "\"ASSERT\"";

		// translate optional label expression
		String stmt = "";
		RacNode n2 = null;
		JExpression expr = self.throwMessage();
		if (expr != null) {
			CType type = expr.getApparentType();
			String val = defaultValue(type);
			String v2 = varGen.freshVar();

			// FRioux - Experimental test for efficiency (begin)

//			if(!Main.aRacOptions.oldSemantics()){
				transx = new TransExpression2(varGen, ctx, expr, v2, typeDecl, "JMLAssertError");
				n2 = transx.stmt(false).incrIndent();
//			}
//			else{
//				TransExpression trans2 = new TransExpression(varGen,ctx,expr,v2,typeDecl);
//				n2 = trans2.wrappedStmt(val,val).incrIndent();
//			}

			// FRioux - Experimental test for efficiency (end)

			stmt = "  " + type + " " + v2 + " = " + val + ";\n$1\n";
			msg = "\"ASSERT with label: \" + " + v2;
		}

		// compose assertion check code
		JStatement result = RacParser.parseStatement(
				"do {\n" +
				"  if (" + isActive() + ") {\n" +
				"    JMLChecker.enter();\n" + 
				"    java.util.Set " + VN_ERROR_SET + 
				" = new java.util.HashSet();\n" +
				"    boolean " + v1 + " = false;\n" + 
				"$0\n" +
				stmt + // eval of optional label expression
				"    if (!" + v1 + ") {\n" +
				"      JMLChecker.exit();\n" +
				"      throw new JMLAssertError(" + msg + ", \"" + 
				TransType.ident() + "\", \"" +
				methodDecl.ident() + "\", " +
				VN_ERROR_SET + ");\n" +
				"    }\n" +
				"    JMLChecker.exit();\n" +
				"  }\n" +
				"}\n" +
				"while (false);",
				n1, n2);
		self.setAssertionCode(result);
	}

	/** 
	 * Translates the given JML <code>debug</code> statement and
	 * stores the translated code into the AST node.
	 * The translated code has the following form:
	 *
	 * <pre>
	 * [[debug E;]] ==
	 *   do {
	 *      [[E]]
	 *   } while (false);
	 * </pre>
	 *
	 * <pre><jml>
	 * also
	 *   requires self != null;
	 *   modifies self.*;
	 *   ensures self.assertionCode() != null;
	 * </jml></pre>
	 *
	 * @see #visitJmlAssumeStatement(JmlAssumeStatement)
	 * @see #translate()
	 */
//	public void visitJmlDebugStatement(JmlDebugStatement self) {
//	// translate expression part
//	RacContext ctx = RacContext.createPositive();
//	JExpression expr = self.expression();
//	String var = varGen.freshVar();
//	TransExpression trans = 
//	new TransExpressionSideEffect(varGen, expr, var, typeDecl);
//	RacNode node = trans.stmt();

//	// optional var declaration for expression result
//	String varDeclOpt = "";
//	CType type = expr.getApparentType();
//	if (!type.isVoid()) {
//	varDeclOpt = "      " + type + " " + var + " = " + 
//	defaultValue(type) + ";\n";
//	}

//	// error message
//	String msg = "\"An exception is thrown by a debug statement\"";
//	String loc = "";
//	TokenReference tref = self.getTokenReference();
//	if (tref != null && tref != TokenReference.NO_REF) {
//	loc = escapeString(tref.toString());
//	}

//	// compose code
//	JStatement result = RacParser.parseStatement(
//	"do {\n" +
//	"  if (" + isActive() + ") {\n" +
//	"    JMLChecker.enter();\n" + 
//	"    java.util.Set " + VN_ERROR_SET + 
//	" = new java.util.HashSet();\n" +
//	"    try {\n" +
//	varDeclOpt +
//	"$0\n" +
//	"      JMLChecker.exit();\n" +
//	"    } catch (java.lang.Throwable rac$e$debug) {\n" +
//	"      JMLChecker.exit();\n" +
//	"      " + VN_ERROR_SET + ".add(\"" + loc + "\");\n" +
//	"      " + VN_ERROR_SET + ".add(rac$e$debug.toString());\n" +
//	"      throw new JMLDebugError(" + msg + ", \"" + 
//	TransType.ident() + "\", \"" +
//	methodDecl.ident() + "\", " +
//	VN_ERROR_SET + ");\n" +
//	"    }\n" + // catch
//	"  }\n" + // if
//	"}\n" +
//	"while (false);",
//	node.incrIndent().incrIndent().incrIndent());

//	self.setAssertionCode(result);
//	}

	/**
	 * Returns true if the given assume (or assert) statement is
	 * checkable. The statement is <em>checkable</em> if it is not a
	 * redundant specification or the command line option
	 * <code>noredundancy</code> is not turned on.
	 */
	private static /*@ spec_public pure @*/ 
	boolean isCheckable(JmlAssertOrAssumeStatement clause) {
		return !(clause.isRedundantly() && Main.aRacOptions.noredundancy());
	}

	/**
	 * Returns true if the given hence_by statement is
	 * checkable. The statement is <em>checkable</em> if it is not a
	 * redundant specification or the command line option
	 * <code>noredundancy</code> is not turned on.
	 */
//	private static /*@ spec_public pure @*/ 
//	boolean isCheckable(JmlHenceByStatement clause) {
//		return !(clause.isRedundantly() && Main.aRacOptions.noredundancy());
//	}

	/**
	 * Returns true if the given loop invariant is checkable. The
	 * statement is <em>checkable</em> if it is not a redundant
	 * specification or the command line option
	 * <code>noredundancy</code> is not turned on. In addition, an
	 * informal variant function is not checkable.
	 */
//	private static /*@ spec_public pure @*/ 
//	boolean isCheckable(JmlLoopSpecification clause) {
//		boolean result =
//			!(clause.isRedundantly() && Main.aRacOptions.noredundancy());
//		if (result && (clause instanceof JmlVariantFunction)) {
//			result = !((JmlVariantFunction) clause).isInformal();
//		}
//		return result;
//	}

	/** 
	 * Translates the JML <code>assume</code> statement and stores the
	 * translated assertion check code into the AST node.  An
	 * <code>assume_redundantly</code> statement is translated only if
	 * the command-line option <code>noredundancy</code> is turned off
	 * (which is the default). Note that the assumptions are checked
	 * only if the runtime option
	 * <code>reportAssumptionViolation</code> is set (which is the
	 * default).  The translated assertion code has the following
	 * form:
	 *
	 * <pre>
	 * [[assume E;]] == 
	 *   if (JMLChecker.reportAssumptionViolation()) {
	 *     boolean v = false;
	 *     [[E, v]]
	 *     if (!v) {
	 *       throw new JMLAssumeError();
	 *     }
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 * also
	 *   requires self != null;
	 *   modifies self.*;
	 *   ensures isCheckable(self) ==> self.assertionCode() != null;
	 * </jml></pre>
	 *
	 * @see #visitJmlAssertStatement(JmlAssertStatement)
	 * @see #translate()
	 */
	public void visitJmlAssumeStatement(JmlAssumeStatement self) {
		if (!isCheckable(self))
			return;
		//@ assume !self.isRedundantly() || !Main.racOptions.noredundancy();

		// translate predicate part
		RacPredicate pred = new RacPredicate(self.predicate());
		String v1 = varGen.freshVar();
		RacContext ctx = RacContext.createPositive();

		// FRioux - Experimental test for efficiency (begin)

		RacNode n1 = null;

//		if(!Main.aRacOptions.oldSemantics()){
			TransExpression2 transx = new TransExpression2(varGen, ctx, pred, v1, typeDecl, "JMLAssumeError");
			n1 = transx.stmt(true).incrIndent();
//		}
//		else{
//			TransPredicate trans = new TransPredicate(varGen, ctx, pred, v1, typeDecl);
//			n1 = trans.wrappedStmt().incrIndent();
//		}

		// FRioux - Experimental test for efficiency (end)

		String msg = "\"ASSUME\"";

		// translate optional label expression
		String stmt = "";
		RacNode n2 = null;
		JExpression expr = self.throwMessage();
		if (expr != null) {
			CType type = expr.getApparentType();
			String val = defaultValue(type);
			String v2 = varGen.freshVar();

			// FRioux - Experimental test for efficiency (begin)

//			if(!Main.aRacOptions.oldSemantics()){
				transx = new TransExpression2(varGen, ctx, expr, v2, typeDecl, "JMLAssumeError");
				n2 = transx.stmt(false).incrIndent();
//			}
//			else{
//				TransExpression trans2 = new TransExpression(varGen,ctx,expr,v2,typeDecl);
//				n2 = trans2.wrappedStmt(val, val).incrIndent();
//			}

			// FRioux - Experimental test for efficiency (end)

			stmt = "  " + type + " " + v2 + " = " + val + ";\n$1\n";
			msg = "\"ASSUME with label: \" + " + v2;
		}

		// compose assertion check code
		JStatement result = RacParser.parseStatement(
				"do {\n" +
				"  if (" + isActive() + 
				" && JMLChecker.reportAssumptionViolation()) {\n" +
				"    JMLChecker.enter();\n" + 
				"    java.util.Set " + VN_ERROR_SET + 
				" = new java.util.HashSet();\n" +
				"    boolean " + v1 + " = false;\n" +
				"$0\n" +
				stmt + // eval of optional label expression
				"    if (!" + v1 + ") {\n" +
				"      JMLChecker.exit();\n" +
				"      throw new JMLAssumeError(" + msg + ", \"" + 
				TransType.ident() + "\", \"" +
				methodDecl.ident() + "\", " +
				VN_ERROR_SET + ");\n" +
				"    }\n" +
				"    JMLChecker.exit();\n" +
				"  }\n" +
				"}\n" +
				"while (false);",
				n1, n2);
		self.setAssertionCode(result);
	}

	/** Translates the given JML guarded statement. Currently not
	 * supported yet. */
	public void visitJmlGuardedStatement(JmlGuardedStatement self) {
	}

	/** Translates the given JML <code>hence_by</code> and stores the
	 * translated assertion check code into the AST node.  An
	 * <code>hence_by_redundantly</code> statement is translated only
	 * if the command-line option <code>noredundancy</code> is turned
	 * off (which is the default). The translated assertion code has
	 * the following form:
	 *
	 * <pre>
	 * [[hence_by P;]] == 
	 *   boolean v = false;
	 *   [[P, v]]
	 *   if (!v) {
	 *      throw new JMLHenceByError();
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 * also
	 *   requires self != null;
	 *   modifies self.*;
	 *   ensures isCheckable(self) ==> self.assertionCode() != null;
	 * </jml></pre>
	 *
	 * @see #visitJmlAssertStatement(JmlAssertStatement)
	 * @see #translate()
	 * supported yet. */
//	public void visitJmlHenceByStatement(JmlHenceByStatement self) {
//	if (!isCheckable(self))
//	return;
//	//@ assume !self.isRedundantly() || !Main.racOptions.noredundancy();

//	// translate predicate part
//	RacPredicate pred = new RacPredicate(self.predicate());
//	String v1 = varGen.freshVar();
//	RacContext ctx = RacContext.createPositive();
//	TransPredicate trans = new TransPredicate(varGen, ctx, pred, v1, typeDecl);
//	RacNode n1 = trans.wrappedStmt().incrIndent();
//	String msg = "\"HENCE_BY\"";

//	// compose assertion check code
//	JStatement result = RacParser.parseStatement(
//	"do {\n" +
//	"  if (" + isActive() + ") {\n" +
//	"    JMLChecker.enter();\n" + 
//	"    java.util.Set " + VN_ERROR_SET + 
//	" = new java.util.HashSet();\n" +
//	"    boolean " + v1 + " = false;\n" +
//	"$0\n" +
//	"    if (!" + v1 + ") {\n" +
//	"      JMLChecker.exit();\n" +
//	"      throw new JMLHenceByError(" + msg + ", \"" + 
//	TransType.ident() + "\", \"" +
//	methodDecl.ident() + "\", " +
//	VN_ERROR_SET + ");\n" +
//	"    }\n" +
//	"    JMLChecker.exit();\n" +
//	"  }\n" +
//	"}\n" +
//	"while (false);",
//	n1);
//	self.setAssertionCode(result);
//	}


	/** Translates the given JML loop statement and stores the
	 * instrumented code into the AST node of <code>self</code>.  The
	 * pretty-printer is supposed to print the instrumented code
	 * instead of the original AST node. For the structure of
	 * instrumented code, refer to methods <code>transWhileLoop</code>,
	 * <code>transDoLoop</code>, and <code>transForLoop</code>.
	 *
	 * <pre><jml>
	 *   also
	 *     requires self != null;
	 *     modifies self.*;
	 * </jml></pre>
	 *
	 * @see #transWhileLoop()
	 * @see #transDoLoop()
	 * @see #transForLoop()
	 * @see RacPrettyPrinter#visitJmlLoopStatement()
	 */
//	public void visitJmlLoopStatement(JmlLoopStatement self) {
//	// generate code for checking loop invariants and variants
//	RacNode checkInv = invariantCheckCode(self.loopInvariants());
//	RacNode checkVar = variantCheckCode(self.variantFunctions());

//	// no need to check both invariant and variant?
//	if (checkInv == null && checkVar == null) {
//	// translate the loop statement itself
//	self.stmt().accept(this);
//	} else {
//	// instrument the loop statement with check code
//	JLoopStatement lstmt = self.loopStmt();
//	if (lstmt instanceof JWhileStatement) {
//	transWhileLoop(self, checkInv, checkVar);
//	} else if (lstmt instanceof JDoStatement) {
//	transDoLoop(self, checkInv, checkVar);
//	} else {
//	transForLoop(self, checkInv, checkVar);
//	}
//	}
//	}

	/**
	 * Returns code that checks the given loop invariants. If there is
	 * no invariant to check (e.g., all are redundant invariants and
	 * the command-line option <code>--noredundancy</code> is turned
	 * on), <code>null</code> is returned. Otherwise, the following
	 * form of code is returned.
	 *
	 * <pre>
	 *  if (IS_ACTIVE()) {
	 *    JMLChecker.enter();
	 *    boolean v = false;
	 *    [[I,v]]
	 *    JMLChecker.exit();
	 *    if (!v) {
	 *      throw new JMLLoopInvariantError(...);
	 *    }
	 *  }
	 * </pre>
	 *
	 * 
	 * <pre><jml>
	 * requires invs != null;
	 * ensures (* \result may be null *);
	 * </jml></pre>
	 */
//	private RacNode invariantCheckCode(JmlLoopInvariant[] invs) {
//	JExpression pred = conjoinInvariants(invs);
//	if (pred == null) {
//	return null;
//	}

//	// translate the invariant, i.e., [[I, var]]
//	String var = varGen.freshVar();
//	RacNode node = null;
//	{
//	RacContext ctx = RacContext.createPositive();
//	TransPredicate trans = new TransPredicate(varGen,ctx,pred,var,typeDecl);
//	node = trans.wrappedStmt().incrIndent();
//	}

//	// generate and return code for checking invariant
//	String msg = "\"LOOP INVARIANT\"";
//	return RacParser.parseStatement(
//	"if (" + isActive() + ") {\n" +
//	"  JMLChecker.enter();\n" + 
//	"  java.util.Set " +VN_ERROR_SET+ " = new java.util.HashSet();\n" +
//	"  boolean " + var + " = false;\n" +
//	"$0\n" +
//	"  JMLChecker.exit();\n" +
//	"  if (!" + var + ") {\n" +
//	"    throw new JMLLoopInvariantError(" + msg + ", \"" + 
//	TransType.ident() + "\", \"" +
//	methodDecl.ident() + "\", " +
//	VN_ERROR_SET + ");\n" +
//	"  }\n" + // if
//	"}",
//	node);
//	}

	/**
	 * Returns code that checks the given loop variants. If there is
	 * no variant to check (e.g., all are redundant variants and
	 * the command-line option <code>--noredundancy</code> is turned
	 * on), <code>null</code> is returned. Otherwise, the following
	 * form of code is returned.
	 *
	 * <pre>
	 *  if (IS_ACTIVE()) {
	 *    JMLChecker.enter();
	 *    int v1 = 0;
	 *    [[E1,v1]]
	 *    JMLChecker.exit();
	 *    if (v1 < 0 || (!isFirst && v1 >= vo1)) {
	 *      throw new JMLLoopVariantError(...);
	 *    }
	 *    vo1 = v1;
	 *    isFirst = false;
	 *  }
	 *  ...
	 *  if (IS_ACTIVE()) {
	 *    JMLChecker.enter();
	 *    int vn = 0;
	 *    [[E1,vn]]
	 *    JMLChecker.exit();
	 *    if (vn < 0 || (!isFirst && vn >= von)) {
	 *      throw new JMLLoopVariantError(...);
	 *    }
	 *    von = vn;
	 *    isFirst = false;
	 *  }
	 * </pre>
	 *
	 * The declaration of temporary variables such as vo1, ..., von,
	 * and isFirst is piggybacked through the name field of the
	 * RacNode, and is of the following string.
	 * 
	 * <pre>
	 *  boolean isFirst = true;
	 *  int vo1 = 0;
	 *  ...
	 *  int von = 0;
	 * </pre>
	 * 
	 * <pre><jml>
	 * requires vars != null;
	 * ensures (* \result may be null *);
	 * </jml></pre>
	 */
//	private RacNode variantCheckCode(JmlVariantFunction[] vars) {
//	if (vars.length <= 0) {
//	return null;
//	}

//	String isFirst = varGen.freshVar();
//	String varDecl = "boolean " + isFirst + " = true;\n";
//	RacNode checkCode = null;

//	for (int i = 0; i < vars.length; i++) {
//	if (!isCheckable(vars[i])) 
//	continue;

//	JmlSpecExpression expr = vars[i].specExpression();

//	// generate initializer, i.e., int ovar = 0; 
//	String ovar = varGen.freshVar();
//	varDecl = varDecl + "int " + ovar + " = 0;\n";

//	// generate checking and update code, i.e.,
//	// int nvar = 0;
//	// [[E, nvar]]
//	// if (nvar < 0 || (!isFirst && nvar >= ovar)) {
//	//   throw new JMLLoopVariantError();
//	// }
//	// ovar = nvar;
//	// isFirst = false;
//	//
//	String nvar = varGen.freshVar();
//	RacContext ctx = RacContext.createPositive();
//	TransExpression trans = new TransExpression(varGen,ctx,expr,nvar,typeDecl);
//	RacNode node = trans.stmt();
//	String msg = "\"LOOP VARIANT(old=\" + " + ovar + 
//	"+ \", new=\" + " + nvar + "+ \")\"";
//	checkCode = RacParser.parseStatement(
//	(checkCode == null ? "" : "$0\n") +
//	"if (" + isActive() + ") {\n" +
//	"  JMLChecker.enter();\n" + 
//	"  java.util.Set " + VN_ERROR_SET +
//	" = new java.util.HashSet();\n" +
//	"  int " + nvar + " = 0;\n" +
//	"$1\n" +
//	"  JMLChecker.exit();\n" +
//	"  if (0 > " + nvar + " || (!" + isFirst + " && " +
//	nvar + " >= " + ovar + ")) {\n" +
//	"    " + VN_ERROR_SET + ".add(\"\\t" + 
//	escapeString(expr.getTokenReference().toString())
//	+ "\");\n" +
//	"    throw new JMLLoopVariantError(" + msg + ", \"" +
//	TransType.ident() + "\", \"" +
//	methodDecl.ident() + "\", " +
//	VN_ERROR_SET + ");\n" +
//	"  }\n" +
//	"  " + ovar + " = " + nvar + ";\n" +
//	"  " + isFirst + " = false;\n" +
//	"}", 
//	checkCode, node.incrIndent());
//	}

//	if (checkCode == null) {
//	return null;
//	} else {
//	// piggyback var decls in the name field
//	checkCode.setName(varDecl);
//	return checkCode;
//	}        
//	}

	/** Translates the given JML loop statement with the given
	 * invariant check code and variant check code. The given loop
	 * statement is supposed to be a while loop.  The translated code
	 * is stored into the AST node of <code>self</code>, and it has
	 * the following form:
	 *
	 * <pre>
	 * [[while (B) S]] == 
	 *   {
	 *     boolean v = false;
	 *     <<varDecl>>
	 *     while (true) {
	 *       <<checkInv>>
	 *       <<checkVar>>
	 *       if (!(B)) {
	 *         v = true;
	 *         break;
	 *       }
	 *       S
	 *     }
	 *     if (!v) {
	 *       <<checkInv>>
	 *     }
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 *   requires self != null;
	 *   requires checkInv != null || checkVar != null;
	 *   requires self.loopStmt() instanceof JForStatement;
	 *   modifies self.*;
	 * </jml></pre>
	 *
	 * @see #variantCheckCode(JmlVariantFunction[])
	 * @see #invariantCheckCode(JmlLoopInvariant[])
	 */
//	private void transWhileLoop(JmlLoopStatement self, 
//	RacNode checkInv,
//	RacNode checkVar) {
//	JWhileStatement stmt = (JWhileStatement) self.loopStmt();
//	JExpression cond = stmt.cond();
//	JStatement body = stmt.body();

//	// recursively translate the body
//	body.accept(this);

//	// local vars to be used to instrument while statement
//	boolean hasInv = checkInv != null;
//	if (hasInv) {
//	checkInv.incrIndent().incrIndent();
//	}
//	RacNode varDecl = null;
//	boolean hasVar = checkVar != null;
//	if (hasVar) {
//	varDecl = RacParser.parseStatement(checkVar.name());
//	varDecl.incrIndent();
//	checkVar.incrIndent().incrIndent();
//	}

//	// instrument while statement
//	String label = self.isLabeled() ? (self.label() + ": ") : "";
//	JStatement result = RacParser.parseStatement(
//	"{\n" +
//	(hasVar ? "$4" : "") + // varDecl 
//	"  " + label + "while (true) {\n" +
//	(hasInv ? "$2\n" : "") + // checkInv
//	(hasVar ? "$3\n" : "") + // checkVar
//	"    if (!($0)) {\n" + // cond
//	"      break;\n" +
//	"    }\n" + 
//	"$1\n" + // body
//	"  }\n" +
//	(hasInv ?
//	("  {\n" +
//	"$2\n" + // checkInv
//	"  }\n") : "") +
//	"}",
//	new Object[] { cond, body, checkInv, checkVar, varDecl } );

//	self.setAssertionCode(result);
//	}

	/** Translates the given JML loop statement with the given
	 * invariant check code and variant check code. The given loop
	 * statement is supposed to be a while loop.  The translated code
	 * is stored into the AST node of <code>self</code>, and it has
	 * the following form:
	 *
	 * <pre>
	 * [[while (B) S]] == 
	 *   {
	 *     <<varDecl>>
	 *     while (true) {
	 *       <<checkInv>>
	 *       <<checkVar>>
	 *       if (!(B)) {
	 *         break;
	 *       }
	 *       S
	 *     }
	 *     <<checkInv>>
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 *   requires self != null;
	 *   requires checkInv != null || checkVar != null;
	 *   requires self.loopStmt() instanceof JDoStatement;
	 *   modifies self.*;
	 * </jml></pre>
	 *
	 * @see #variantCheckCode(JmlVariantFunction[])
	 * @see #invariantCheckCode(JmlLoopInvariant[])
	 */
//	private void transDoLoop(JmlLoopStatement self, 
//	RacNode checkInv,
//	RacNode checkVar) {
//	JDoStatement stmt = (JDoStatement) self.loopStmt();
//	JExpression cond = stmt.cond();
//	JStatement body = stmt.body();

//	// recursively translate the body
//	body.accept(this);


//	// local vars to be used to instrument do statement
//	boolean hasInv = checkInv != null;
//	if (hasInv) {
//	checkInv.incrIndent().incrIndent();
//	}
//	RacNode varDecl = null;
//	boolean hasVar = checkVar != null;
//	if (hasVar) {
//	varDecl = RacParser.parseStatement(checkVar.name());
//	varDecl.incrIndent();
//	checkVar.incrIndent().incrIndent();
//	}

//	// instrument do statement
//	String label = self.isLabeled() ? (self.label() + ": ") : "";
//	JStatement result = RacParser.parseStatement(
//	"{\n" +
//	(hasVar ? "$4" : "") + // vardecl 
//	"  " + label + "while (true) {\n" +
//	(hasInv ? "$2\n" : "") + // checkInv
//	(hasVar ? "$3\n" : "") + // checkVar
//	"$1\n" + // body
//	"    if (!($0)) {\n" + // cond
//	"      break;\n" +
//	"    }\n" + 
//	"  }\n" +
//	(hasInv ?
//	("  {\n" +
//	"$2\n" + // checkInv
//	"  }\n") : "") +
//	"}",
//	new Object[] { cond, body, checkInv, checkVar, varDecl } );

//	self.setAssertionCode(result);
//	}

	/** Translates the given JML loop statement with the given
	 * invariant check code and variant check code. The given loop
	 * statement is supposed to be a for loop.  The translated code is
	 * stored into the AST node of <code>self</code>, and it has the
	 * following form:
	 *
	 * <pre>
	 * [[for (I1, ..., In; B; U1, ..., Un) S]] == 
	 *   {
	 *     I1, ..., In;
	 *     boolean vExit = false;
	 *     boolean vIncr = false;
	 *     <<varDecl>>
	 *     while (true) {
	 *       if (vIncr) {
	 *         U1, ..., Un;
	 *       } else {
	 *         vIncr = true;
	 *       }
	 *       <<checkInv>>
	 *       <<checkVar>>
	 *       if (!(B)) {
	 *         vExit = true;
	 *         break;
	 *       }
	 *       S
	 *     }
	 *     if (!vExit) {
	 *       <<checkInv>>
	 *     }
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 *   requires checkInv != null || checkVar != null;
	 *   requires self.loopStmt() instanceof JForStatement;
	 *   modifies self.*;
	 * </jml></pre>
	 *
	 * @see #variantCheckCode(JmlVariantFunction[])
	 * @see #invariantCheckCode(JmlLoopInvariant[])
	 */
//	private void transForLoop(/*@ non_null @*/ JmlLoopStatement self, 
//	RacNode checkInv,
//	RacNode checkVar) {
//	JForStatement stmt = (JForStatement) self.loopStmt();
//	JExpression cond = stmt.cond();
//	JStatement body = stmt.body();
//	JStatement incr = stmt.incr();
//	JStatement init = stmt.init();

//	// recursively translate the body
//	body.accept(this);

//	// local vars to be used to instrument for statement
//	boolean hasInv = checkInv != null;
//	if (hasInv) {
//	checkInv.incrIndent().incrIndent();
//	}
//	RacNode varDecl = null;
//	boolean hasVar = checkVar != null;
//	if (hasVar) {
//	varDecl = RacParser.parseStatement(checkVar.name());
//	varDecl.incrIndent();
//	checkVar.incrIndent().incrIndent();
//	}

//	// instrument for statement
//	String varIncr = varGen.freshVar();
//	String label = self.isLabeled() ? (self.label() + ": ") : "";
//	JStatement result = RacParser.parseStatement(
//	"{\n" +
//	(init != null ? "$0;\n" : "") + // init
//	"  boolean " + varIncr + " = false;\n" +
//	(hasVar ? "$6" : "") + // varDecl
//	"  " + label + "while (true) {\n" +
//	"    if (" + varIncr + ") {\n" +
//	(incr != null ? "$2;\n" : "") + // incr
//	"    } else {\n" +
//	"      " + varIncr + " = true;\n" +
//	"    }\n" +
//	(hasInv ? "$4\n" : "") + // checkInv
//	(hasVar ? "$5\n" : "") + // checkVar
//	(cond == null ? "" : 
//	("    if (!($1)) {\n" + // cond
//	"      break;\n" +
//	"    }\n")) + 
//	"$3\n" + // body
//	"  }\n" +
//	(hasInv ?
//	("  {\n" +
//	"$4\n" + // checkInv
//	"  }\n") : "") +
//	"}",
//	new Object[] { init, cond, incr, body, 
//	checkInv, checkVar, varDecl } );

//	self.setAssertionCode(result);
//	}

	/**
	 * Conjoins the given loop invariants and returns the result.  If
	 * there is no invariant to conjoin (e.g., all are redundant
	 * invariants and the command-line option
	 * <code>--noredundancy</code> is turned on), <code>null</code> is
	 * returned. 
	 *
	 * <pre><jml>
	 * requires invs != null;
	 * ensures (* \result may be null *);
	 * </jml></pre>
	 */
//	private JExpression conjoinInvariants(JmlLoopInvariant[] invs) {
//	JExpression left = null;
//	for (int i = 0; i < invs.length; i++) {
//	if (!isCheckable(invs[i]))
//	continue;
//	RacPredicate p = new RacPredicate(invs[i].predicate());
//	if (left == null)
//	left = p;
//	else
//	left = new JConditionalAndExpression(org.multijava.util.compiler.TokenReference.NO_REF, left, p);
//	}
//	return left;
//	}

	/** Translates the given JML invariant statement. Currently not
	 * supported yet. */
	public void visitJmlInvariantStatement(JmlInvariantStatement self) {
	}

	/** Translates the given JML nondeterministic choice
	 * statement. Currently not supported yet. */
	public void visitJmlNondetChoiceStatement(JmlNondetChoiceStatement self) {
	}

	/** Translates the given JML nondeterministic if statement. 
	 * Currently not supported yet. */
	public void visitJmlNondetIfStatement(JmlNondetIfStatement self) {
	}

	/** Translates the given JML specification statement. Currently
	 * not supported yet. */
	public void visitJmlSpecStatement(JmlSpecStatement self) {
	}

	/** 
	 * Translates the JML <code>set</code> statement and stores the
	 * translated assertion check code into the AST node.  The
	 * translated assertion code has the following structure:
	 *
	 * <pre>
	 * [[set g = E;]] ==
	 *   { 
	 *      T g; 
	 *      [[E,g]]
	 *      ghost$g(g);      // dynamic call to setter
	 *   }
	 * [[set g *= E;]] ==
	 *   { 
	 *      T g = ghost$v(); // dynamic call to getter
	 *      T v; 
	 *      [[E,v]]
	 *      g *= v;          // commound assignments (e.g., +=, -=, etc).
	 *      ghost$v(g);      // dynamic call to setter
	 *   }
	 * </pre>
	 *
	 * <pre><jml>
	 * also
	 *   requires self != null;
	 *   modifies self.*;
	 *   ensures self.assertionCode() != null;
	 * </jml></pre>
	 *
	 * @see TransClass
	 * @see TransInterface
	 * @see TransType
	 */
//	public void visitJmlSetStatement(JmlSetStatement self) {
//	// initialize local variables
//	JAssignmentExpression expr = 
//	(JAssignmentExpression) self.assignmentExpression();

//	// no attempt to execute if the ghost field is from JDK classes
//	CClass cls = ((JClassFieldExpression) expr.left()).getField().owner();
//	if (TransUtils.excludedFromInheritance(cls)) {
//	return;
//	}

//	// This is assured by the type checker.
//	//@ assume expr.right() instanceof JClassFieldExpression;
//	CType type = expr.left().getApparentType();
//	String initVal = defaultValue(type);

//	// translate RHS of the assignment expression
//	RacContext ctx = RacContext.createPositive();
//	String rvar = varGen.freshVar();
//	RacNode rnode = new TransExpression(varGen, ctx, expr.right(), rvar, typeDecl)
//	.wrappedStmt(initVal, initVal).incrIndent();

//	// build translated code
//	JClassFieldExpression lexpr = (JClassFieldExpression) expr.left();
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
//	"  " + ivar + operator(expr) + rvar + ";\n" +
//	"$2\n" +
//	"}",
//	new TransExpression(varGen, ctx, lexpr, ivar,typeDecl)
//	.wrappedStmt(initVal, initVal).incrIndent(),
//	rnode, 
//	ghostFieldSetter(lexpr, ivar).incrIndent());
//	} else {
//	result = RacParser.parseStatement(
//	"{\n" +
//	"  " + typeName + " " + rvar + " = " + initVal + ";\n" +
//	"$0\n" +
//	"$1\n" +
//	"}",
//	rnode, ghostFieldSetter(lexpr, rvar).incrIndent());
//	}

//	// store the result into the original AST node
//	self.setAssertionCode(result);
//	}

	/**
	 * Returns Java source code that makes a dynamic call to the
	 * setter method of the given ghost field, <code>fieldExpr</code>,
	 * to set the ghost value to the value of the given variable,
	 * <code>argVar</code>. Assume that <code>fieldExpr</code> is of
	 * the form "E.g", where E's type is T. Then, the returned code
	 * has the following general structure:
	 *
	 * <pre>
	 *  T v;
	 *  [[E, v]]
	 *  rac$invoke("T", v, "g", typeOf(argVar), wrapped(argVar));
	 * </pre>
	 *
	 * <pre><jml>
	 * requires fieldExpr != null && argVar != null && 
	 *          (* fieldExpr is a reference to a ghost field *);
	 * ensures \result != null;
	 * </jml></pre>
	 */
//	private RacNode ghostFieldSetter(JClassFieldExpression fieldExpr,
//			String argVar) {
//		return getGhostFieldSetter(fieldExpr, argVar, varGen);
//	}

	/**
	 * Returns Java source code that makes a dynamic call to the
	 * setter method of the given ghost field, <code>fieldExpr</code>,
	 * to set the ghost value to the value of the given variable,
	 * <code>argVar</code>.
	 */
//	public static RacNode getGhostFieldSetter(
//	JClassFieldExpression fieldExpr,
//	String argVar,
//	VarGenerator varGen) {

//	// decide the receiver of dynamic call (to ghost field setter)
//	RacNode receiverNode = null;
//	String receiver = "";
//	if (isStatic(fieldExpr)) {
//	receiver = "null";
//	} else {
//	receiverNode = transPrefix(varGen, fieldExpr);
//	receiver = receiverNode == null ? "this" : receiverNode.name();
//	}

//	// determine the target class and method names for dynamic
//	// call.  If fieldExpr is an instance of JSuperExpression
//	// (e.g, super.g), fieldExpr.getField().owner() returns the
//	// superclass; so, no special handling is needed for super
//	// calls.
//	CClass cls = fieldExpr.getField().owner(); // owner of ghost field
//	String className = TransUtils.dynamicCallName(cls);
//	String methodName = MN_GHOST + fieldExpr.ident() + "$" + cls.ident();

//	if (TransExpression.canMakeStaticCall(fieldExpr, receiver)) {
//	// return code for static (non-dynamic) call
//	if (isStatic(fieldExpr)) {
//	receiver = className;
//	} else {
//	if (cls.isInterface()) {
//	receiver = "((" + className + ") " + 
//	"JMLChecker.getSurrogate(\"" + className + 
//	"\", rac$forName(\"" + className + "\"), " +
//	receiver+ "))";
//	}
//	}
//	return RacParser.parseStatement(
//	(receiverNode == null ? "" : "$0\n") + // prefix eval code
//	receiver + "." + methodName + 
//	"((" + TransUtils.toString(fieldExpr.getType()) + ") " +
//	argVar + ");",
//	receiverNode);
//	}

//	// record that we need to generate a dynamic call method
//	needDynamicInvocationMethod();

//	// return dyanmic call code
//	CType type = fieldExpr.getApparentType();
//	return RacParser.parseStatement(
//	(receiverNode == null ? "" : "$0\n") +     // prefix code
//	"try {\n" +
//	"  rac$invoke(\"" + className + "\", " +   // target class
//	receiver + ", \"" +                     // receiver
//	methodName + "\", " +                   // target method
//	"new java.lang.Class[] { " +            // parameter types
//	TransUtils.typeToClass(type) + "}, " +                
//	"new java.lang.Object[] { " +                     // arguments
//	TransUtils.wrapValue(type, argVar) + "});\n" +
//	"} catch (java.lang.Exception " + 
//	varGen.freshCatchVar() + ") {\n" +
//	"}\n",
//	receiverNode);
//	}

	/**
	 * Translates the prefix expression of the given field reference
	 * expression, <code>fieldExpr</code>. The expression is assumed
	 * to be a reference to a non-static ghost field. If there is no
	 * need to translate the prefix (e.g., super, T.super, this,
	 * T.this, T), then <code>null</code> is returned; otherwise, the
	 * translated code of the following form is returned.
	 *
	 * <pre>
	 *  T v;
	 *  [[E, v]]
	 * </pre>
	 *
	 * where <code>E</code> is the prefix expression, and
	 * <code>v</code> is a temporary variable. The name of the
	 * temporary variable, <code>v</code>, is stored in the name field
	 * of the result object.
	 *
	 * <pre><jml>
	 * requires varGen != null && fieldExpr != null;
	 * ensures (* \result may be null *);
	 * </jml></pre>
	 *
	 */
//	private static RacNode transPrefix(VarGenerator varGen,
//			JClassFieldExpression fieldExpr) {
//		// Java Language Specification on Field Access
//		// JLS 15.11
//		// FieldAccess:
//		//   Primary . Identifier
//		//   super . Identifier
//		//   ClassName . super . Identifier
//		//
//		// JLS 18.8 
//		// Primary:        String val = defaultValue(type);
//		//   PrimaryNoNewArray
//		//   ArrayCreationExpression
//		// PrimaryNoNewArray:
//		//   Literal
//		//   Type . class 
//		//   void . class 
//		//   this
//		//   ClassName.this
//		//   ( Expression )
//		//   ClassInstanceCreationExpression
//		//   FieldAccess
//		//   MethodInvocation
//		//   ArrayAccess
//
//		// As the type checker adds "this" for null prefix, the prefix
//		// is not null. And neither "T.super" and "T.this" is possible
//		// because jmlrac does not translate inner classes yet.
//
//		JExpression prefix = fieldExpr.prefix();
//		if (prefix instanceof JSuperExpression ||    // super or T.super
//				(prefix instanceof JThisExpression  &&   // this or T.this
//						!TransType.isInterface()) ||            
//						prefix instanceof JTypeNameExpression) { // T
//			return null;
//		}
//		// note that in an interface, "this" should be translated into
//		// the delegee field of the surrogate class; thus the
//		// conjunction for the JThisExpression.
//
//		RacContext ctx = RacContext.createPositive();
//		CType type = prefix.getApparentType();
//		String var = varGen.freshVar();
//		RacNode code = RacParser.parseStatement(
//				type + " " + var + " = " + 
//				defaultValue(type) + ";\n" +
//				"$0\n",
//				new TransExpression(varGen, ctx, prefix, var, null).stmt());
//		code.setName(var);
//		return code;
//	}

	/** Returns true if the given field expression is a reference to a
	 * static field.
	 *
	 * <pre><jml>
	 * requires expr != null;
	 * </jml></pre>
	 **/
//	private static boolean isStatic(JClassFieldExpression expr) {
//		return hasFlag(((CField)expr.getField()).modifiers(), ACC_STATIC);
//	}

	/**
	 * Returns the string representation of the assignment operator of
	 * the given assignment expression. E.g., <code>" = "</code> for
	 * simple assignment expression.
	 *
	 * <pre><jml>
	 * requires expr != null;
	 * ensures \result != null && \fresh(\result);
	 * </jml></pre>
	 */
	public static String operator(JAssignmentExpression expr) {
		switch (expr.oper()) {
		case OPE_SIMPLE:
			return " = ";
		case OPE_STAR:
			return(" *= ");
		case OPE_SLASH:
			return(" /= ");
		case OPE_PERCENT:
			return(" %= ");
		case OPE_PLUS:
			return(" += ");
		case OPE_MINUS:
			return(" -= ");
		case OPE_SL:
			return(" <<= ");
		case OPE_SR:
			return(" >>= ");
		case OPE_BSR:
			return(" >>>= ");
		case OPE_BAND:
			return(" &= ");
		case OPE_BXOR:
			return(" ^= ");
		case OPE_BOR:
			return(" |= ");
		}

		//@ unreachable;
		return " = ";
	}

	/** 
	 * Translates the JML <code>unreachable</code> statement.
	 * The translated assertion code has the following form:
	 *
	 * <pre>
	 * [[unreachable;]] == check(v [&& !assumed]);
	 * </pre>
	 *
	 * The optional conjunction in the check statement is generated only
	 * if the statement is in the scope of any <code>assume</code> statement.
	 * This is because the assert condition must hold only if the assume 
	 * conditions hold.
	 * The flag <code>assumed</code> is set by <code>assume</code> 
	 * statements. 
	 *
	 * @see #visitJmlAssumeStatement(JmlAssumeStatement)
	 */
	public void visitJmlUnreachableStatement(JmlUnreachableStatement self) {
		StringBuffer c = new StringBuffer();
		c.append("do {\n");
		c.append("  if (" + isActive() + ") {\n");
		c.append("    java.util.Set ");
		c.append(VN_ERROR_SET);
		c.append(" = new java.util.HashSet();\n");
		if (self.getTokenReference() != null) {
			c.append("     " + VN_ERROR_SET + ".add(\"\\t");
			c.append(escapeString(self.getTokenReference().toString()));
			c.append("\");\n");
		}
		c.append("    throw new JMLUnreachableError(");
		c.append("\"UNREACHABLE\", \"" +
				TransType.ident() + "\", \"" +
				methodDecl.ident() + "\", " +
				VN_ERROR_SET + ");\n");
		c.append("  }\n");
		c.append("}\n");
		c.append("while (false);");
		self.setAssertionCode(RacParser.parseStatement(c.toString()));
	}

	// ----------------------------------------------------------------------
	// VISITORS FOR JAVA STATEMENTS
	// ----------------------------------------------------------------------

	/** Translates the given Java assert statement. */
	public void visitAssertStatement(JAssertStatement self) {
	}

	/** Translates the given Java block statement. */
	public void visitBlockStatement(JBlock self) {
		JStatement[] body = self.body();
		visitCompoundStatement(body);
	}

	/** Translates the given Java constructor statement. */
	public void visitConstructorBlock(JConstructorBlock self) {
		JStatement[] body = self.body();
		self.explicitSuper();
		JStatement blockCall = self.blockCall();
		if( blockCall != null ) {
			blockCall.accept( this );
		}
		visitCompoundStatement(body);
	}

	/** Translates the given Java break statement. */
	public void visitBreakStatement(JBreakStatement self) {
	}

	/** Translates the given Java compound statement. */
	public void visitCompoundStatement(JCompoundStatement self) {
		JStatement[] body = self.body();
		visitCompoundStatement(body);
	}

	/** Translates the given Java compound statement. */
	public void visitCompoundStatement(JStatement[] body) {
		for (int i = 0; i < body.length; i++) {
			body[i].accept(this);
		}
	}

	/** Translates the given Java continue statement. */
	public void visitContinueStatement(JContinueStatement self) {
	}

	/** Translates the given Java empty statement. */
	public void visitEmptyStatement(JEmptyStatement self) {
	}

	/** Translates the given Java expression list statement. */
	public void visitExpressionListStatement(JExpressionListStatement self) {
	}

	/** Translates the given Java expression statement. */
	public void visitExpressionStatement(JExpressionStatement self) {
	}

	/** Translates the given Java if statement. */
	public void visitIfStatement(JIfStatement self) { 
		JStatement thenClause = self.thenClause();
		JStatement elseClause = self.elseClause();
		thenClause.accept(this);
		if (elseClause != null) {
			elseClause.accept(this);
		}
	}

	/** Translates the given Java labeled statement. */
	public void visitLabeledStatement(JLabeledStatement self) {
		JStatement stmt = self.stmt();
		stmt.accept(this);
	}

	/** Translates the given Java for statement. */
	public void visitForStatement(JForStatement self) { 
		JStatement init = self.init();
		JStatement incr = self.incr();
		JStatement body = self.body();
		if (init != null) {
			init.accept(this);
		}
		if (incr != null) {
			incr.accept(this);
		}
		body.accept(this);
	}

	/** Translates the given Java do statement. */
	public void visitDoStatement(JDoStatement self) {
		JStatement body = self.body();
		body.accept(this);
	}

	/** Translates the given Java while statement. */
	public void visitWhileStatement(JWhileStatement self) { 
		JStatement body = self.body();
		body.accept(this);
	}

	/** Translates the given Java return statement. */
	public void visitReturnStatement(JReturnStatement self) {
	}

	/** Translates the given Java switch statement. */
	public void visitSwitchStatement(JSwitchStatement self) {
		JSwitchGroup[] groups = self.groups();
		for (int i = 0; i < groups.length; i++) {
			groups[i].accept(this);
		}
	}

	/** Translates the given Java switch group statement. */
	public void visitSwitchGroup(JSwitchGroup self) {
		JStatement[] stmts = self.getStatements();
		for (int i = 0; i < stmts.length; i++) {
			stmts[i].accept(this);
		}
	}

	/** Translates the given Java synchronized statement. */
	public void visitSynchronizedStatement(JSynchronizedStatement self) {
		JBlock body = self.body();
		body.accept(this);
	}

	/** Translates the given Java throw statement. */
	public void visitThrowStatement(JThrowStatement self) {
	}

	/** Translates the given Java try/catch statement. */
	public void visitTryCatchStatement(JTryCatchStatement self) {
		JBlock tryClause = self.tryClause();
		JCatchClause[] catchClauses = self.catchClauses();
		tryClause.accept(this);
		for (int i = 0; i < catchClauses.length; i++) {
			catchClauses[i].accept(this);
		}
	}

	/** Translates the given Java try/finally statement. */
	public void visitTryFinallyStatement(JTryFinallyStatement self) {
		JBlock tryClause = self.tryClause();
		JBlock finallyClause = self.finallyClause();
		tryClause.accept(this);
		if (finallyClause != null) {
			finallyClause.accept(this);
		}
	}

	/** Translates the given Java type declaration statement. */
	public void visitTypeDeclarationStatement(JTypeDeclarationStatement self) {
	}

	/** Translates the given Java variable declaration statement. */
	public void visitVariableDeclarationStatement(
			JVariableDeclarationStatement self) {
	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/** Records that a ghost field inheritance mechanism is needed. */
//	private static void needDynamicInvocationMethod() {
//		TransType.dynamicInvocationMethodNeeded = true;
//	}

	/** Return the default value of the type <code>type</code>. */
	public static String defaultValue(CType type) {
		if (type instanceof CNumericType)
			return (type == JmlStdType.Bigint) ?
					"java.math.BigInteger.ZERO" : "0";
		else if (type == CStdType.Boolean)
			return "false";
		else 
			return "null";
	}

	/**
	 * Returns a string representation of the condition that tests if
	 * the given type of assertion is active. Assertion checking is
	 * active only when the instance has completed its construction.
	 */
	protected /*@ non_null @*/ String isActive() {
		return "JMLChecker.isActive(JMLChecker.INTRACONDITION) && " +
		VN_CLASS_INIT + 
		(methodDecl.isStatic() ? "" : " && " + VN_INIT) +
		(methodDecl.isConstructor() ? 
				" && " + VN_CONSTRUCTED + "()" : ""); 
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** variable generator to generate fresh local variables */
	protected /*@ non_null @*/ VarGenerator varGen;

	/** type declaration to which the method belongs */
	protected /*@ non_null @*/ JTypeDeclarationType typeDecl;

	/** method declaration whose body is being translated */
	protected /*@ non_null @*/ JmlMethodDeclaration methodDecl;

	/** method body to be translated */
	protected /*@ non_null @*/ JBlock body;
}

