/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AJML
 *
 * AJML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * AJML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with AJML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: Main.java,v 1.0 2009/02/20 16:37:23 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: TransExpression2.java,v 1.26 2007/11/04 16:12:10 f_rioux Exp $
 * by Frederic Rioux (based on Yoonsik Cheon's work)
 */

package org.jmlspecs.ajmlrac;

import java.util.Stack;

import org.jmlspecs.ajmlrac.qexpr.TransQuantifiedExpression;
import org.jmlspecs.checker.JmlElemTypeExpression;
import org.jmlspecs.checker.JmlFreshExpression;
import org.jmlspecs.checker.JmlInformalExpression;
import org.jmlspecs.checker.JmlInvariantForExpression;
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
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CField;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFieldGetterMethod;
import org.multijava.mjc.CMethod;
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
import org.multijava.util.compiler.TokenReference;

/**
 * A RAC visitor class to translate JML expressions into AspectJ source code.
 * 
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public/*@ non_null_by_default */ class TransExpression2 extends
AbstractExpressionTranslator {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Constructs an instance and translates the given expression.
	 * 
	 * @param varGen
	 *            variable generator to be used for generating fresh variable
	 *            names necessary in the translated code.
	 * @param expr
	 *            expression to be translated.
	 * @param resultVar
	 *            variable to store the result. In the translated code, the
	 *            result of the expression is stored in the variable whose name
	 *            given by this parameter.
	 */
	public TransExpression2(VarGenerator varGen, RacContext ctx,
			JExpression expr, String resultVar, JTypeDeclarationType typeDecl, String errorType) {

		this.varGen = varGen;
		this.resultVar = resultVar;
		this.expression = expr;
		this.context = ctx;
		this.typeDecl = typeDecl;
		this.errorType = errorType;

		resultingExpression = "";
		thisIs = TransType.ident();
		translated = false;
		this.tokenReference = new StringBuffer();
	}

	// ----------------------------------------------------------------------
	// ACCESSORS
	// ----------------------------------------------------------------------

	/**
	 * Returns the result of translating the expression.
	 * 
	 * @return translation result
	 */
	public RacNode stmt(boolean wrapped) {
		perform();
		String resultStr = resultVar + " = " + resultVar;
		if (!"".equals(resultingExpression)) {
			resultStr = resultVar + " = " + resultingExpression + ";";
		} else {
			LOG("!!! EMPTY RESULT !!! - visitor is not complete - dummy code generated");
		}

		RacNode node = RacParser.parseStatement(resultStr);
		// while(!quantifiedStatementsStack.isEmpty()){
		// node = RacParser.parseStatement("$0\n$1", (RacNode)
		// quantifiedStatementsStack.pop(), node);
		// }
		node = addPrebuiltNode(node);
		// hemr
//		if (wrapped) {
//		node = wrap(node);
//		}

		return node;

	}

	protected String stmtAsString() {
		perform();
		String resultStr = resultVar + " = " + resultVar; //FIXME
		if (!"".equals(resultingExpression)) {
			resultStr = resultingExpression;
		} else {
			LOG("!!! EMPTY RESULT !!! - visitor is not complete - dummy code generated");
		}
		return resultStr;
	}

	protected RacNode wrap(RacNode node){
		TokenReference tok = expression.getTokenReference();

		// Ensures uniqueness of variables
		String eVar = varGen.freshVar() + "$nonExec";
		String tVar = varGen.freshVar() + "$cause";

		//TODO refactor and get rid of code duplication
		if(tok == null){
			LOG("!!! Token reference is null !!!");       	
			return RacParser.parseStatement("// Alternative Translation\ntry {\n"
					+ "$0"

					// Top-level translation should catch NonExecutableException
					// in order to make the entire clause true (or false)
					+ (!isInner ? "\n} catch (JMLNonExecutableException " + eVar + ") {\n\t" + resultVar + " = "
							+ (Main.aRacOptions.mustBeExecutable()?"false":"true") + ";" : "")

							+ " \n} catch (Throwable " + tVar + ") {\n\tJMLChecker.exit();\n\tthrow new JMLEvaluationError(\"" 
							+ "Invalid Expression\"" 
							+ ", " + "new " + errorType + "(" + tVar + ")); \n}", node.incrIndent());
		} else {
			return RacParser.parseStatement("// Alternative Translation\ntry {\n"
					+ "$0"

					// Top-level translation should catch NonExecutableException
					// in order to make the entire clause true (or false)
					+ (!isInner ? "\n} catch (JMLNonExecutableException " + eVar + ") {\n\t" + resultVar + " = " 
							+ (Main.aRacOptions.mustBeExecutable()?"false":"true") + ";" : "")

							+ " \n} catch (Throwable " + tVar + ") {\n\tJMLChecker.exit();\n\tthrow new JMLEvaluationError(\"" 
							+ "Invalid Expression in \\\"" + tok.name() 
							+ "\\\", line " + tok.line() 
							+ ", character " + tok.column() 
							+ "\", " + "new " + errorType + "(" + tVar + ")); \n}", node.incrIndent());
		}
	}

	public RacNode addPrebuiltNode(RacNode initial){
		RacNode node = initial;
		while(!prebuiltStatementsStack.isEmpty()){
			//LOG("Took a quantified node...");
			node = RacParser.parseStatement("$0\n$1", (RacNode) prebuiltStatementsStack.pop(), node);
		}
		return node;
	}

	public boolean hasPrebuiltNodes(){
		return !prebuiltStatementsStack.isEmpty();
	}

	/**
	 * Translates the current expression into a sequence of Java statements that
	 * evaluate and store the result in the result variable. The result variable
	 * is assumed to be declared in the outer scope.
	 */
	protected void perform() {
		//LOG("~~~~~ " + TransType.ident());
		LOG("@----- IN { " + this.getClass().toString() + " }");
		try{
			if (!translated) {
				translated = true;
				LOG(" --> " + expression.getClass().toString());
				expression.accept(this);
				properlyEvaluated = true;
			}
		} catch (NonExecutableExpressionException e) {
			LOG("NE@ - " + e.getMessage());
			handleExceptionalTranslation(e);
		} catch (NotImplementedExpressionException e) {
			LOG("NI@ - " + e.getMessage());
			handleExceptionalTranslation(e);
		} catch (NotSupportedExpressionException e) {
			LOG("NS@ - " + e.getMessage());
			handleExceptionalTranslation(e);
		}
		LOG("@----- OUT - " + resultingExpression);
	}

	protected void handleExceptionalTranslation(PositionnedExpressionException e){
		properlyEvaluated = false;
		reportedException = e;
		notExecutableClauseWarn(e.getTok(), e.getMessage());      
		RETURN_RESULT(Main.aRacOptions.mustBeExecutable()?"false":"true"); //i.e. drop the whole clause
	}
	
	public String getTokenReference(){
		return this.tokenReference.toString();
	}

	// ----------------------------------------------------------------------
	// VISITORS FOR TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translates the given RAC predicate.
	 */
	public void visitRacPredicate(RacPredicate self) {
		// TODO: Could maybe do more fancy processing as a RAC predicate
		// contains useful info.
		TokenReference tref = self.getTokenReference();
		boolean isEqualToDefaultRequiresTokenRef = AspectUtil.getInstance().getDefaultRequiresClauseTokenRefereces().contains(tref.toString());
		boolean isEqualToDefaultEnsuresTokenRef = AspectUtil.getInstance().getDefaultEnsuresClauseTokenRefereces().contains(tref.toString());

		String fileExt = (typeDecl.getCClass().sourceFile().getAbsolutePath().endsWith(".jml")? ".jml": ".java");
		if(!(isEqualToDefaultRequiresTokenRef) && !(isEqualToDefaultEnsuresTokenRef)){
			if(this.tokenReference.length() > 0){
				this.tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+fileExt+":"+tref.line()).append(")");	
			}
			else{
				this.tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+fileExt+":"+tref.line()).append(")");
			}
		}
//        String msg = escapeString(tref.toString());
		LOG(" --> " + self.specExpression().getClass().toString());
		self.specExpression().accept(this);
	}

	/**
	 * Translates the given JML predicate.
	 */
	public void visitJmlPredicate(JmlPredicate self) {
		LOG(" --> " + self.specExpression().getClass().toString());
		self.specExpression().accept(this);
	}

	/**
	 * Translates the given JML spec expression.
	 */
	public void visitJmlSpecExpression(JmlSpecExpression self) {
		LOG(" --> " + self.expression().getClass().toString());
		self.expression().accept(this);
	}

	// ----------------------------------------------------------------------
	// JML PRIMARY
	// ----------------------------------------------------------------------

	/**
	 * NOT SUPPORTED
	 * Translates a JmlNonNullElementsExpression.
	 * <i>The operator \nonnullelements can be used to assert that an array and its
	 * elements are all non-null</i>
	 * True if the array is not null and all of its elements are non-null. False otherwise.
	 */
	public void visitJmlNonNullElementsExpression( JmlNonNullElementsExpression self ) {
		// FIXME: clean-up: remove the if and unreachable code.
//		if(false) {
//			throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlNonNullElementsExpression"));
//		} else {
			JmlSpecExpression expr = self.specExpression();
			LOG(" --> " + expr.getClass().toString());
			expr.accept(this);
			String exprStr = (String) GET_RESULT();
			String resultStr = "JMLRacUtil.nonNullElements(" + exprStr + ")";
			RETURN_RESULT(resultStr);
//		}
	}

	/**
	 * Translated a JmlElemTypeExpression.
	 * <i>The \elemtype operator returns the most-specific static type shared by all elements 
	 * of its array argument</i>
	 */
	public void visitJmlElemTypeExpression( JmlElemTypeExpression self ) {
		JmlSpecExpression expr = self.specExpression();
		LOG(" --> " + expr.getClass().toString());
		expr.accept(this);
		String exprStr = (String) GET_RESULT();
		String resultStr = exprStr + ".getComponentType()";
		RETURN_RESULT(resultStr);
	}

	/**
	 * Translates a JmlNotModifiedExpression expression. (Not executable)
	 */
	public void visitJmlNotModifiedExpression( JmlNotModifiedExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlNotModifiedExpression"));
	}

	/**
	 * Translates a JmlNotAssignedExpression expression. (Not executable)
	 */
	public void visitJmlNotAssignedExpression( JmlNotAssignedExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlNotAssignedExpression"));
	}

	/**
	 * Translates a JmlFreshExpression expression. (Not executable)
	 */
	public void visitJmlFreshExpression( JmlFreshExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlFreshExpression"));
	}

	/**
	 * Translates a JmlInformalExpression expression. (Not executable)
	 */
	public void visitJmlInformalExpression(JmlInformalExpression self) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlInformalExpression"));
	}

	/**
	 * NOT SUPPORTED
	 * <i>The \invariant_for operator returns true just when its argument satisfies
	 * the invariant of its static type.</i>
	 */
	public void visitJmlInvariantForExpression(  JmlInvariantForExpression self ) {
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlInvariantForExpression"));
	}

	public void visitJmlIsInitializedExpression( JmlIsInitializedExpression self) {
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlIsInitializedExpression"));
	}

	public void visitJmlLabelExpression( JmlLabelExpression self ){
		// TODO
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlLabelExpression"));

//		// translate the spec expression
//		LOG(" --> " + self.specExpression().getClass().toString());
//		self.specExpression().accept(this);
//		Strig expr = (String) GET_RESULT();

//		// build error message
//		TokenReference tref = self.getTokenReference();
//		String msg = "label: '" + escapeString(self.ident()) + "'(" + 
//		escapeString(tref.toString()) + ")";

//		String result = null;

//		if(self.isPosLabel()){
//		String result = ...
//		}else{
//		String result = ...
//		}

//		RETURN_RESULT(result);

	}

	public void visitJmlLockSetExpression( JmlLockSetExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlLockSetExpression"));
	}

	public void visitJmlOldExpression( JmlOldExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlOldExpression"));
	}

	public void visitJmlPreExpression( JmlPreExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlPreExpression"));
	}

	public void visitJmlReachExpression( JmlReachExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlReachExpression"));
	}

	public void visitJmlResultExpression( JmlResultExpression self ) {
		throw(new NonExecutableExpressionException(self.getTokenReference(), "JmlResultExpression"));
	}

	public void visitJmlSetComprehension( JmlSetComprehension self ) {
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlSetComprehension"));
	}

	public void visitJmlSpecQuantifiedExpression( JmlSpecQuantifiedExpression self ) {
		if("JMLAssertError".equals(errorType) || "JMLAssumeError".equals(errorType))
		{
			throw(new NotImplementedExpressionException(self.getTokenReference(), "JmlSpecQuantifiedExpression in JMLAssert or JMLAssume statements"));
		}
		TransExpression2 t = new TransExpression2(varGen, context, expression, resultVar, typeDecl, errorType);
		translateSpecQuantifiedExpression(t, self);	
	}

	// So that TransPostExpression2 can use a TransPostExpression2 instance
	protected void translateSpecQuantifiedExpression(TransExpression2 t, JmlSpecQuantifiedExpression self){
		t.isInner = true;
		t.thisIs = thisIs; //"this" issue for anonymous class
		String var = varGen.freshVar();
		TransQuantifiedExpression trans = new TransQuantifiedExpression(varGen, context, self, var, t);
		String node = trans.translateAsString();
		CType type = self.getApparentType();
		String quantifierEvaluation = "       "+TransUtils.toString(type) + " " + var + " = " + TransUtils.defaultValue(type) + " ;\n"+node+"\n       return " + var + ";";

		//TODO
		//Ensure generated code is always compilable (e.g. when used in JMLAssert/Assume statement inside a method body)

		String aClass = varGen.freshVar();
		quantifierEvaluation = "       class " + aClass + "{public " + TransUtils.toString(type) + " eval(" + evaluatorPDef + "){\n"+quantifierEvaluation+"\n       }}\n"+"       "+ aClass + " " + var + "Evaluator = new " + aClass + "();";

		//quantifierEvaluation = RacParser.parseStatement("JMLRacExpressionEvaluator " + var + "Evaluator = new JMLRacExpressionEvaluator(){public boolean eval(" + evaluatorPDef + "){\n$0\n}};", quantifierEvaluation);
//		prebuiltStatementsStack.push(quantifierEvaluation);
		int qtfid = AspectUtil.getInstance().getUniqueVarGenForQuantifier();	
		AspectUtil.getInstance().appendQuantifierUniqueID("/*"+CN_RAC_QUANTIFIER_ID+qtfid+"*/");
		AspectUtil.getInstance().appendQuantifierInnerClasses(quantifierEvaluation+"/*"+CN_RAC_QUANTIFIER_ID+qtfid+"*/");
//		System.out.println("######################RESULT Quantifier <BEGIN>");
//		System.out.println(quantifierEvaluation+"/*"+CN_RAC_QUANTIFIER_ID+qtfid+"*/");
//    	System.out.println("######################RESULT Quantifier <END>");
        	
		RETURN_RESULT("/*"+CN_RAC_QUANTIFIER_ID+qtfid+"*/"+var + "Evaluator.eval(" + evaluatorPUse + ")");
  
	}

	/**
	 * Translated a JmlTypeExpression.
	 * <i>The operator \type can be used to mark types in expressions.</i>
	 */
	public void visitJmlTypeExpression( JmlTypeExpression self ) {
		CType type = self.type();
		String result = ""; 
		if (type.isPrimitive() || type.isVoid()) {
			result = translatePrimitive(type);
		} else {
			result = TransUtils.toString(type) + ".class";
		}
		RETURN_RESULT(result);
	}

	/**
	 * Translated a JmlTypeExpression.
	 * <i>The operator \typeof returns the most-specific dynamic type of an expression's value.</i>
	 */
	public void visitJmlTypeOfExpression( JmlTypeOfExpression self ) {
		String result = ""; 

		JmlSpecExpression expr = self.specExpression();
		CType type = expr.getType();

		if (type.isPrimitive() || type.isVoid()) {
			result = translatePrimitive(type);
		} else {
			LOG(" --> " + expr.getClass().toString());
			expr.accept(this);
			String exprStr = (String) GET_RESULT();    
			result = exprStr + ".getClass()";
		}
		RETURN_RESULT(result);

	}

	private String translatePrimitive(CType type){
		String result = "";
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
		return result;

	}

	public void visitJmlMaxExpression( JmlMaxExpression self ) {
		throw(new NotSupportedExpressionException(self.getTokenReference(), "JmlMaxExpression"));
	}    


	// ----------------------------------------------------------------------
	// EXPRESSION SYNTAX
	// ----------------------------------------------------------------------

	/**
	 * Translates a Java assignment expression. The JML type checker gurantees
	 * that this be never visited, i.e., assignment expressions are not allowed
	 * in JML expression.
	 */
	public void visitAssignmentExpression(JAssignmentExpression self) {
		throw(new NotSupportedExpressionException(self.getTokenReference(), "JAssignmentExpression"));
	}

	/**
	 * Translates a Java compound assignment expression. The JML type checker
	 * gurantees that this be never visited, i.e., assignment expressions are
	 * not allowed in JML expression.
	 */
	public void visitCompoundAssignmentExpression(JAssignmentExpression self) {
		throw(new NotSupportedExpressionException(self.getTokenReference(), "compound JAssignmentExpression"));
	}

	/**
	 * Translates various types of supported binary expression into
	 * <code>left opr right</code>. 
	 * -JBinaryArithmeticExpression 
	 * -- JAddExpression (+) 
	 * -- JBitwiseExpression (&, |, ^) 
	 * -- JDivideExpression (/) 
	 * -- JMinusExpression (-) 
	 * -- JModuloExpression (%) 
	 * -- JMultExpression (*) 
	 * -- JShiftExpression (<<, >>, >>>) 
	 * - JConditionalAndExpression (&&) 
	 * - JConditionalOrExpression (||) 
	 * - JEqualityExpression (==, !=) 
	 * - JRelationalExpression (<, <=, >, >=)
	 */
	protected void visitBinaryExpression(JBinaryExpression self, String oper) {

		String leftStr;
		String rightStr;

		JExpression left = self.left();
		// @ assert left != null;
		LOG(" --> " + left.getClass().toString());
		left.accept(this);
		leftStr = (String) GET_RESULT();

		JExpression right = self.right();
		// @ assert right != null;
		LOG(" --> " + right.getClass().toString());
		right.accept(this);
		rightStr = (String) GET_RESULT();

		// Handle bigints
		if(left.getApparentType() == JmlStdType.Bigint){
			String[] strArray = TransUtils.applyBigintBinOperator(oper);
			RETURN_RESULT ("(" + leftStr + strArray[0] + rightStr + strArray[1] + ")");
			return;
		}

		generateBinaryExpression(oper, leftStr, rightStr);
	}

	/**
	 * Generates a binary expression.
	 */
	protected void generateBinaryExpression(String oper, String left, String right) {
		String resultStr = "(" + left + oper + right + ")";
		RETURN_RESULT(resultStr);
	}

	/**
	 * Translates an equality expression into <code>left opr right</code>.
	 */
	public void visitEqualityExpression(JEqualityExpression self) {
		visitBinaryExpression(self, (self.oper() == OPE_EQ) ? " == " : " != ");
	}

	/**
	 * Translates a conditional "and" expression into <code>left && right</code>.
	 */
	public void visitConditionalAndExpression(JConditionalAndExpression self) {
		visitBinaryExpression(self, " && ");
	}

	/**
	 * Translates a conditional "or" expression into <code>left || right</code>.
	 */
	public void visitConditionalOrExpression(JConditionalOrExpression self) {
		visitBinaryExpression(self, " || ");
	}

	/**
	 * Translates a bitwise expression into <code>left opr ritgh</code>.
	 */
	public void visitBitwiseExpression(JBitwiseExpression self) {
		String opStr = null;
		switch (self.oper()) {
		case OPE_BAND:
			opStr = " & ";
			break;
		case OPE_BOR:
			opStr = " | ";
			break;
		case OPE_BXOR:
			opStr = " ^ ";
			break;
		default:
			fail("Unknown bitwise expression");
		}
		visitBinaryExpression(self, opStr);
	}

	/**
	 * Translates an add expression.
	 */
	public void visitAddExpression(JAddExpression self) {
		visitBinaryExpression(self, " + ");
	}

	/**
	 * Translates a minus expression.
	 */
	public void visitMinusExpression(JMinusExpression self) {
		visitBinaryExpression(self, " - ");
	}

	/**
	 * Translates a multiplication expression.
	 */
	public void visitMultExpression(JMultExpression self) {
		visitBinaryExpression(self, " * ");
	}

	/**
	 * Translates a divide expression.
	 */
	public void visitDivideExpression(JDivideExpression self) {
		visitBinaryExpression(self, " / ");
	}

	/**
	 * Translates a modulo division expression.
	 */
	public void visitModuloExpression(JModuloExpression self) {
		visitBinaryExpression(self, " % ");
	}

	/**
	 * Translates a shift expression.
	 */
	public void visitShiftExpression(JShiftExpression self) {
		String opStr = null;
		int oper = self.oper();
		if (oper == OPE_SL) {
			opStr = " << ";
		} else if (oper == OPE_SR) {
			opStr = " >> ";
		} else {
			opStr = " >>> ";
		}
		visitBinaryExpression(self, opStr);
	}

	/**
	 * Translates java relational expression.
	 */
	public void visitRelationalExpression(JRelationalExpression self) {
		String opStr = null;
		switch (self.oper()) {
		case OPE_LT:
			opStr = " < ";
			break;
		case OPE_LE:
			opStr = " <= ";
			break;
		case OPE_GT:
			opStr = " > ";
			break;
		case OPE_GE:
			opStr = " >= ";
			break;
		default:
			fail();
		}
		visitBinaryExpression(self, opStr);
	}

	/**
	 * Translates a JML relational expression.
	 */
	public void visitJmlRelationalExpression(JmlRelationalExpression self) {

		if (self.isSubtypeOf()) {

			JExpression left = self.left();
			// @ assert left != null;
			LOG(" --> " + left.getClass().toString());
			left.accept(this);
			String leftStr = (String) GET_RESULT();

			JExpression right = self.right();
			// @ assert right != null;
			LOG(" --> " + right.getClass().toString());
			right.accept(this);
			String rightStr = (String) GET_RESULT();

			RETURN_RESULT(rightStr + ".isAssignableFrom(" + leftStr + ")");

		} else if (self.isEquivalence()) {
			visitBinaryExpression(self, " == ");
		} else if (self.isNonEquivalence()) {
			visitBinaryExpression(self, " != ");
		} else if (self.isImplication() || self.isBackwardImplication()) {
			JExpression left = self.left();
			// @ assert left != null;
			LOG(" --> " + left.getClass().toString());
			left.accept(this);
			String leftStr = (String) GET_RESULT();

			JExpression right = self.right();
			// @ assert right != null;
			LOG(" --> " + right.getClass().toString());
			right.accept(this);
			String rightStr = (String) GET_RESULT();

			if (self.isImplication()) {
				generateBinaryExpression(" || ", "!(" + leftStr + ")", rightStr);
			} else {
				generateBinaryExpression(" || ", "!(" + rightStr + ")", leftStr);
			}
		} else {
			visitRelationalExpression(self);
		}
	}

	/**
	 * Generates a tertiary (conditional) expression.
	 */
	protected void generateTertiaryExpression(String condition, String left,
			String right) {
		String resultStr = "(" + condition + " ? " + left + " : " + right + ")";
		RETURN_RESULT(resultStr);
	}

	/**
	 * Translates a conditional expression.
	 */
	public void visitConditionalExpression(JConditionalExpression self) {

		JExpression cond = self.cond();
		// @ assert cond != null;
		LOG(" --> " + cond.getClass().toString());
		cond.accept(this);
		String condStr = (String) GET_RESULT();

		JExpression left = self.left();
		// @ assert left != null;
		LOG(" --> " + left.getClass().toString());
		left.accept(this);
		String leftStr = (String) GET_RESULT();

		JExpression right = self.right();
		// @ assert right != null;
		LOG(" --> " + right.getClass().toString());
		right.accept(this);
		String rightStr = (String) GET_RESULT();

		generateTertiaryExpression(condStr, leftStr, rightStr);
	}

	/**
	 * Translates a cast expression.
	 */
	public void visitCastExpression(JCastExpression self) {
		JExpression expr = self.expr();
		CType dest = self.getApparentType();
		CType var = expr.getApparentType();

		String result = "";
		if (expr.getApparentType() == CStdType.Null) {
			result = "(" + TransUtils.toString(dest) + ") null";
		} else {
			LOG(" --> " + expr.getClass().toString());
			expr.accept(this);
			String[] strArray;
			strArray = TransUtils.applyBigintCast(dest, var, TransUtils.toString(dest));
			result = strArray[0] + (String) GET_RESULT() + strArray[1];
		}

		RETURN_RESULT("(" + result + ")");
	}

	/**
	 * Translates a Java unary promotion expression.
	 */
	public void visitUnaryPromoteExpression(JUnaryPromote self) {

		JExpression expr = self.expr();

		CType typeSelf = self.getApparentType();
		CType typeExpr = expr.getApparentType();

		LOG(" --> " + expr.getClass().toString());
		expr.accept(this);
		String resultStr = GET_RESULT();

		if (!(expr instanceof JNullLiteral)) {
			RETURN_RESULT("(" + TransUtils.applyUnaryPromoteExpression(typeSelf, typeExpr, "(" + resultStr + ")") + ")");
		}
	}

	/**
	 * Translates a JUnaryExpression expression into <code>opr expr</code>.
	 */
	public void visitUnaryExpression(JUnaryExpression self) {

		JExpression expr = self.expr();
		// @ assert expr != null;
		LOG(" --> " + expr.getClass().toString());
		expr.accept(this);

		// Handle bigints
		if(expr.getApparentType() == JmlStdType.Bigint){
			switch (self.oper()) {
			case OPE_PLUS:
				RETURN_RESULT(GET_RESULT());
				break;
			case OPE_LNOT:
				context.changePolarity();
				RETURN_RESULT("!(" + GET_RESULT() + ")");
				break;
			case OPE_MINUS:
				RETURN_RESULT(GET_RESULT() + TransUtils.applyBigintUnOperator("-"));
				break;
			case OPE_BNOT:
				RETURN_RESULT(GET_RESULT() + TransUtils.applyBigintUnOperator("~"));
				break;
			default:
				fail("Unknown unary expression (for bigints)");
			}
		}else{
			switch (self.oper()) {
			case OPE_PLUS:
				RETURN_RESULT("+(" + GET_RESULT() + ")");
				break;
			case OPE_MINUS:
				RETURN_RESULT("-(" + GET_RESULT() + ")");
				break;
			case OPE_BNOT:
				RETURN_RESULT("~(" + GET_RESULT() + ")");
				break;
			case OPE_LNOT:
				//context.changePolarity(); - comment due an null pointer exception - hemr
				RETURN_RESULT("!(" + GET_RESULT() + ")");
				break;
			default:
				fail("Unknown unary expression");
			}
		}
	}

	/**
	 * Translates a JParenthesedExpression expression into <code>( expr )</code>.
	 */
	public void visitParenthesedExpression(JParenthesedExpression self) {
		JExpression expr = self.expr();
		// @ assert expr != null;
		LOG(" --> " + expr.getClass().toString());
		expr.accept(this);
		RETURN_RESULT("(" + (String) GET_RESULT() + ")");
	}

	/**
	 * Translates a Java instanceof expression.
	 */
	public void visitInstanceofExpression(JInstanceofExpression self) {
		JExpression expr = self.expr();
		// @ assert expr != null;
		LOG(" --> " + expr.getClass().toString());
		expr.accept(this);
		RETURN_RESULT(GET_RESULT() + " instanceof " + self.dest());
	}

	/**
	 * Translates a Java local variable expression.
	 */
	public void visitLocalVariableExpression(JLocalVariableExpression self) {
		String ident = self.ident();

		// If exists, use generated RAC field for JML variables such
		// as old variables (see TransMethod.translateLetVarDecl())
		if (self.variable() instanceof JmlVariableDefinition) {
			JmlVariableDefinition var = 
				(JmlVariableDefinition) self.variable();
			if (var.hasRacField()) {
//				CType type = var.getType();
				ident = TransUtils.unwrapObject(var.getType(), var.racField() + ".value()");
			}
		}
		RETURN_RESULT(ident);
	}

	/**
	 * Translates a Java field expression.
	 */
	public void visitFieldExpression(JClassFieldExpression self) {

		// not executable, e.g., fields of model class or interface?
		if (isNonExecutableFieldReference(self)) {
			throw (new NonExecutableExpressionException(self
					.getTokenReference(), "fields of model class or interface"));
		}

		long mods = 0;
		if(self.getField() instanceof CFieldGetterMethod){
			mods = ((CFieldGetterMethod) self.getField()).modifiers(); 
		}
		else{
			mods = ((CField) self.getField()).modifiers(); 
		}
		
		String ident = self.ident();
		String result = "";

		// process prefix
		JExpression prefix = self.prefix();
		LOG(" --> " + prefix.getClass().toString());
		prefix.accept(this);
		String prefixStr = (String) GET_RESULT();
		if (prefixStr == null)
			prefixStr = "";

		// generated fields?
		// TODO what is the purpose of that?
		if (ident.equals(JAV_OUTER_THIS)) {
			result = prefix.getApparentType().getCClass().owner().getType()
			+ ".this";
			RETURN_RESULT(result);
			return;
		}

		// local field
		int index = ident.indexOf("_$");
		if (index != -1) { // local var?
			result = ident.substring(0, index);
		}

		if (specAccessorNeeded(mods)) {
			result = transFieldReference(self, MN_SPEC);

		} else {
			// if model variable, convert this to accessor method call
			// and record this fact by adding the field to modelFieldRefs.
			if (hasFlag(mods, ACC_MODEL)) {
				result = transFieldReference(self, MN_MODEL);
			} else if (hasFlag(mods, ACC_GHOST)) {
				result = transFieldReference(self, MN_GHOST);
			} else if (TransType.genSpecTestFile && !hasFlag(mods, ACC_PUBLIC)) {
				LOG("!@! TEMP DEBUG !@! - ??? genSpecTestFile and not public ???");
				result = transFieldReference(self, MN_MODEL);
				// TODO - No idea what this is all about!!!
//				throw (new NotImplementedExpressionException(self
//						.getTokenReference(),
//				"?? genSpecTestFile and not public ???"));

				// FIXME ??? Use transReference?
				// String id = "prot$" + ident + "$" + typeDecl.ident() + "()";
				// result = transPrefixSpec(prefix, var + " = $0." + id +
				// ";",false);
			} else {
				// TODO is this case needed?
				// FIXME
				result = ident;
				if (prefixStr != null && !prefixStr.equals("") /*
				 * &&
				 * !prefixStr.equals("this")
				 */)
					result = prefixStr + "." + result;
			}
		}
		// LOG("!@! TEMP DEBUG !@! - (JClassFieldExpression) RESULT is: " +
		// result);
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

	/**
	 * Translates a class field expression that references a model,
	 * ghost, spec_public, or spec_protected field. The translated
	 * code dynamically invokes the corresponding accessor method.
	 */

	private String transFieldReference(JClassFieldExpression self,
			String accPrefix) {

		// owner of the referrenced field
		CClass cls = self.getField().owner();

		// no attempt for inheritance, e.g., from JDK classes.
		if (TransUtils.excludedFromInheritance(cls)) {
			throw (new NonExecutableExpressionException(self
					.getTokenReference(), "A reference to field \""
					+ self.ident() + "\""));
		}

		// decide the receiver of dynamic call (model field access method)
		String receiver = "";
		if (isStatic(self)) {
			receiver = "null"; // null for static field
		} else if (TransType.genSpecTestFile
				&& hasFlag(self.getField().getField().modifiers(),
						ACC_PROTECTED)) {
			receiver = receiverForDynamicCall(self);
			accPrefix = "prot$";
		} else {
			receiver = receiverForDynamicCall(self);
			if (receiver.equals("this")
					&& TransType.genSpecTestFile
					&& (!accPrefix.equals("model$") && !accPrefix
							.equals("ghost$"))) {
				receiver = "this.delegee_" + typeDecl.ident() + "()";
			}
		}

		// cn, fully qualified name of the target class
//		String cn = TransUtils.dynamicCallName(cls);
		String cn = "";
		// mn, the name of model/ghost/spec_public accessor method
		// String mn = accPrefix + self.ident() + "$" + cls.ident();
		String mn = self.ident();

		// if possible, return code for static method call
		if (canMakeStaticCall(self, receiver)) {
			if (isStatic(self)) {
				cn = TransUtils.dynamicCallName(cls);
				receiver = cn;
			} else {
//				if (cls.isInterface()) {
//					receiver = "((" + cn + ") " + "JMLChecker.getSurrogate(\""
//					+ cn + "\", rac$forName(\"" + cn + "\"), "
//					+ receiver + "))";
//				}
			}

			// "this" issue for anonymous inner class
			if (isInner && "this".equals(receiver)) {
				// return cn + ".this." + mn + "()";
//				return cn + ".this." + mn;
				return "this." + mn;
			}
			// return receiver + "." + mn + "()";
			return receiver + "." + mn;
		}

		// record that a model field inheritance mechanism is needed
		needDynamicInvocationMethod();

		// return code for dyanmic call to the accessor
		if (isInner && "this".equals(receiver)) {
			// return cn + ".this." + mn + "()";
//			return cn + ".this." + mn;
			return "this." + mn;
		}
		// return receiver + "." + mn + "()";
		return receiver + "." + mn;
//		return TransUtils.unwrapObject(self.getApparentType(), "rac$invoke(\""
//				+ cn + "\", " + receiver + ", \"" + mn + "\", null, null)");
	}

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
	 */
	private String receiverForDynamicCall(/*@ non_null @*/ JExpression expr) {
		JExpression prefix = (expr instanceof JMethodCallExpression) ?
				((JMethodCallExpression)expr).prefix() :
					((JClassFieldExpression)expr).prefix();

				// translate prefix if necessary. As the type checker adds
				// "this" for null prefix, it is not null after typechecking.
				// In addition, both "T.super" and "T.this" are not possible
				// because we are not translating inner classes yet.

				if (prefix instanceof JSuperExpression ||   // super or T.super
						prefix instanceof JThisExpression ||    // this or T.this
						prefix instanceof JTypeNameExpression) {// T
					//return null; // should be interpreted as "this" by the caller
					return "this";
				} else {
//					CType type = prefix.getApparentType();
					LOG(" --> " + prefix.getClass().toString());
					prefix.accept(this);
					String receiver = (String) GET_RESULT();
					return receiver;
				}        
	}

	/** Records that we need to generate the dynamic invocation
	 * method. E.g., to evaluate model, ghost, spec_public, or
	 * spec_protected fields or spec_public or spec_protected methods. */
	private void needDynamicInvocationMethod() {
		TransType.dynamicInvocationMethodNeeded = true;
	}

	/** Returns true if a static (non-dynamic) call can be made to the
	 * given field expression, <code>expr</code>. The given expression
	 * is assumed to be a reference to a model, ghost, spec_public, or
	 * spec_protected field. */
	public static boolean canMakeStaticCall(JClassFieldExpression expr, String receiver) {
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

	/**
	 * Translates a Java method call expression.
	 */
	public void visitMethodCallExpression(JMethodCallExpression self) {
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
//					}
				} else {
					// non-executable model method calls
					throw(new NonExecutableExpressionException(self.getTokenReference(), "A call to model method \"" + cmeth.ident() + "\""));
				} 
				return; // done with model method calls

			} else if (cmeth.isSpecPublic() || cmeth.isSpecProtected()) {
//				if (TransUtils.useReflection() // no -F option?
//				&& TransType.dynamicCallNeeded(meth.owner())) {
//				// true for spec_public/protected method calls
//				translateToDynamicCall(self, false);
//				} else {
				translateToStaticCall(self, ACC_SPEC_PUBLIC);
//				}
				return; // done with spec_public method calls
			}
			// regular method calls with source are translated into 
			// static method calls below.
		}

		// code making static call for normal method calls
		translateToStaticCall(self, 0);
	}

	private void translateToStaticCall(JMethodCallExpression self, long kind) {
		JExpression prefix = self.prefix();
		String ident = self.ident();

		// code for evaluating arguments
		// args has the form: "(v1, v2, ..., vn)"
		String argsStr = "(";
		JExpression[] args = self.args();
		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				LOG(" --> " + args[i].getClass().toString());
				args[i].accept(this);
				argsStr = argsStr + GET_RESULT();
				if (i < args.length - 1) {
					argsStr = argsStr + ", ";
				}
			}
		}
		argsStr = argsStr + ")";

		// compose call statement E1.m(x1,..,xn).
		String result = null;
		// String meth = kind == ACC_SPEC_PUBLIC ?
		// TransUtils.specPublicAccessorName(ident) : ident;
		// this is due to aspects --- henrique rebelo

		String meth = "";

		if (prefix == null) {
			meth = kind == ACC_SPEC_PUBLIC ? (!self.method().owner()
					.getJavaName().equals(
							this.typeDecl.getCClass().getJavaName()) ? self
									.method().owner().getJavaName()
									+ "." + ident : this.typeDecl.getCClass().getJavaName()
									+ "." + ident) : this.typeDecl.getCClass().getJavaName()
									+ "." + ident;
									result = meth + argsStr;
		} else {
			// meth = kind == ACC_SPEC_PUBLIC ? ident :
			// this.typeDecl.getCClass().getJavaName()+"."+ident;
			meth = ident;
			CClass clazz = self.method().owner();
			LOG(" --> " + prefix.getClass().toString());
			prefix.accept(this);
			String prefixStr = (String) GET_RESULT();

			// is interface method method?
//			if (kind == ACC_MODEL && clazz.isInterface()) {
//				// call to the surrogate of the prefix
//				String cn = TransUtils.dynamicCallName(clazz);
//				result = "((" + cn + ") " + "JMLChecker.getSurrogate(\"" + cn
//				+ "\", rac$forName(\"" + cn + "\"), " + prefixStr
//				+ "))." + meth + argsStr;
//			} else {
				// FIXME (ignore "this")
				if (!"".equals(prefixStr)/* && !"this".equals(prefixStr) */) {
					result = prefixStr + "." + meth + argsStr;
				} else {
					result = meth + argsStr;
				}
//			}
		}

		// LOG("!@! TEMP DEBUG !@! - argsStr : " + argsStr);
		// LOG("!@! TEMP DEBUG !@! - translateToStaticCall : " + result);
		RETURN_RESULT(result);
	}
	
//	private void translateToStaticCall2(JMethodCallExpression self, long kind) {
//
//		JExpression prefix = self.prefix();
//		String ident = self.ident();
//
//		// code for evaluating arguments
//		// args has the form: "(v1, v2, ..., vn)"	
//		String argsStr = "(";
//		JExpression[] args = self.args();
//		if(args != null){
//			for (int i = 0; i < args.length; i++) {
//				LOG(" --> " + args[i].getClass().toString());
//				args[i].accept(this);
//				argsStr = argsStr + GET_RESULT();
//				if (i < args.length - 1) {
//					argsStr = argsStr + ", ";
//				}
//			}
//		}
//		argsStr = argsStr + ")";
//
//		// compose call statement E1.m(x1,..,xn).
//		String result = null;
//		String meth = kind == ACC_SPEC_PUBLIC ?	TransUtils.specPublicAccessorName(ident) : ident;
//		if (prefix == null) {
//			result = meth + argsStr;
//		} else {
//			CClass clazz = self.method().owner();
//			LOG(" --> " + prefix.getClass().toString());
//			prefix.accept(this);
//			String prefixStr = (String) GET_RESULT();	
//
//			// is interface method method?
//			if (kind == ACC_MODEL && clazz.isInterface()) {
//				// call to the surrogate of the prefix
//				String cn = TransUtils.dynamicCallName(clazz);
//				result =  "((" +cn+ ") " + "JMLChecker.getSurrogate(\"" +cn+ "\", rac$forName(\"" +cn+ "\"), " + prefixStr + "))." + meth + argsStr;
//			} else{
//				// FIXME (ignore "this")
//				if(!"".equals(prefixStr)/* && !"this".equals(prefixStr)*/){
//					result = prefixStr + "." + meth + argsStr;
//				}else{
//					result = meth + argsStr;
//				}
//			}
//		}
//
//		//LOG("!@! TEMP DEBUG !@! - argsStr : " + argsStr);
//		//LOG("!@! TEMP DEBUG !@! - translateToStaticCall : " + result);
//		RETURN_RESULT(result);
//	}

//	private void translateToDynamicCall(JMethodCallExpression expr,	boolean isModel) {
//
//		needDynamicInvocationMethod();
//
//		// decide the receiver of dynamic call
//		String receiver = "";
//		if (isStatic(expr)) {
//			receiver = "null"; // null for static method
//		} else {
//			receiver = receiverForDynamicCall(expr);
//		}
//
//		// generate code for evaluating arguments; 
//		// args.types has the form: "Class[]  = { T1, ..., Tn }" and 
//		// args.args has the form: "Object[] = { v1, ..., vn }".
//
//		String argsStr = "new java.lang.Object[] { ";
//		String typeStr = "new java.lang.Class[] { ";
//		JExpression[] args = expr.args();
//		CSpecializedType[] ptypes = expr.method().parameters();
//
//		if(args != null){
//			for (int i = 0; i < args.length; i++) {
//
//				CType actualType = ptypes[i].staticType();
//				typeStr = typeStr + TransUtils.typeToClass(actualType);
//
//				LOG(" --> " + args[i].getClass().toString());
//				args[i].accept(this);
//				argsStr = argsStr + TransUtils.wrappedValue(actualType, (String) GET_RESULT());
//
//				if (i < args.length - 1) {
//					argsStr = argsStr + ", ";
//					typeStr = typeStr + ", ";
//				}
//			}
//		}
//		argsStr = argsStr + " }";
//		typeStr = typeStr + " }";
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
//				String result = 
//					TransUtils.unwrapObject(
//							expr.getApparentType(), "rac$invoke(\"" + cn + "\", " +	receiver+ ", \"" + mn + "\", " + typeStr + ", " + argsStr + ")"
//					);
//
//				//LOG("!@! TEMP DEBUG !@! - argsStr : " + argsStr);
//				//LOG("!@! TEMP DEBUG !@! - typeStr : " + typeStr);
//				//LOG("!@! TEMP DEBUG !@! - translateToDynamicCall : " + result);
//				RETURN_RESULT(result);
//	}


	public void visitThisExpression(JThisExpression self) {

		// "this" issue for anonymous inner class
		// if(!isInner){
		String result = isInner ? thisIs + ".this" : "this";
		JExpression prefix = self.prefix();
		if (prefix != null) {
			LOG(" --> " + prefix.getClass().toString());
			prefix.accept(this);
			result = GET_RESULT() + "." + result;
		} else {
			// In interface "this" is translated into the delegee
			// field of the surrogate class.
			if (TransType.genSpecTestFile) {
				result = "this.delegee_" + TransType.ident() + "()";
			}
			if (TransType.isInterface()) {
				// result = "((" + TransType.ident() + ") " + VN_DELEGEE + ")";
				result = "this"; // henriquerebelo - for aspect
				// translation...
			}
		}
		RETURN_RESULT(result);
		// }
		// else{
		// String result = "";
		// RETURN_RESULT(result);
		// }

	}

	public void visitSuperExpression(JSuperExpression self) {
		RETURN_RESULT("super");
	}

	/** Translates a Java prefix expression. The JML type checker
	 * gurantees that this be never visited, i.e., prefix expressions
	 * are not allowed in JML expression. */
	public void visitPrefixExpression( JPrefixExpression self ) {
		throw(new NotSupportedExpressionException(self.getTokenReference(), "JPrefixExpression"));
	}

	/** Translates a Java postfix expression. The JML type checker
	 * gurantees that this be never visited, i.e., postfix expressions
	 * are not allowed in JML expression. */
	public void visitPostfixExpression( JPostfixExpression self ) {
		throw(new NotSupportedExpressionException(self.getTokenReference(), "JPostfixExpression"));
	}

	/**
	 * Translates a Java type name expression
	 */
	public void visitTypeNameExpression( JTypeNameExpression self ) {
		RETURN_RESULT(self.qualifiedName().replace('/', '.'));
	}

	/**
	 * Translates a Java array length expression. The translation
	 * rules for this expression is defined as follows.
	 */
	public void visitArrayLengthExpression( JArrayLengthExpression self ) 
	{
		JExpression prefix = self.prefix();
		LOG(" --> " + prefix.getClass().toString());
		prefix.accept(this);
		RETURN_RESULT(GET_RESULT() + ".length");
	}

	/**
	 * Translates a Java array access expression.
	 */
	public void visitArrayAccessExpression( JArrayAccessExpression self ) 
	{
		JExpression prefix = self.prefix();
		LOG(" --> " + prefix.getClass().toString());
		prefix.accept(this);
		String prefixStr = (String) GET_RESULT();

		JExpression accessor = self.accessor();
		LOG(" --> " + accessor.getClass().toString());
		accessor.accept(this);
		String accessorStr = (String) GET_RESULT();

		RETURN_RESULT(prefixStr + "[" + accessorStr + "]");
	}

	/**
	 * Translates a Java class expression.
	 */
	public void visitClassExpression( JClassExpression self ) 
	{
		RETURN_RESULT(self.prefixType() + ".class");
	}

	/**
	 * Translates an explicit constructor invocation
	 */
	public void visitExplicitConstructorInvocation(
			JExplicitConstructorInvocation self)
	{
		throw(new NotSupportedExpressionException(self.getTokenReference(), "JExplicitConstructorInvocation"));
	}

	/**
	 * Translates a Java name expression.
	 */
	public void visitNameExpression( JNameExpression self ) 
	{
		RETURN_RESULT(self.getName());
	}

	/**
	 * Translates a Java new object expression.
	 */
	public void visitNewObjectExpression( JNewObjectExpression self ) 
	{

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
//					}
				} else {
					// non-executable model method				
					throw(new NonExecutableExpressionException(self.getTokenReference(), "A call to model constructor \"" + cmeth.ident() + "\""));
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
	 */
	private void translateToStaticNewObjectExpression(
			/*@ non_null @*/ JNewObjectExpression self,
			boolean isSpecPublic) {

		// code for evaluating arguments. 
		// args has the form: "(v1, v2, ..., vn)"	
		String argsStr = "(";
		JExpression[] args = self.params();
		if(args != null){
			for (int i = 0; i < args.length; i++) {
				LOG(" --> " + args[i].getClass().toString());
				args[i].accept(this);
				argsStr = argsStr + GET_RESULT();
				if (i < args.length - 1) {
					argsStr = argsStr + ", ";
				}
			}
		}
		argsStr = argsStr + ")";

		// method name to call, either factory or new expression
		CType type = self.getApparentType();
//		String meth = isSpecPublic ?
//				// static factory method
//				type + "." + TransUtils.specPublicAccessorName(MN_INIT) :
//					// new expression
//					"new " + type;
				
		String meth = 
					// new expression
					"new " + type;

				// code for method call
				String result = meth + argsStr;

				//LOG("!@! TEMP DEBUG !@! - translateToStaticNewObjectExpression : " + result);
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
//
//		needDynamicInvocationMethod();
//
//		String receiver = "null"; // null for static method call
//
//		// generate code for evaluating arguments; 
//		// args.types has the form: "new Class[] { T1, ..., Tn }" and 
//		// args.args has the form: "new Object[] { v1, ..., vn }".
//
//		String argsStr = "new java.lang.Object[] { ";
//		String typeStr = "new java.lang.Class[] { ";
//		JExpression[] args = expr.params();
//		CSpecializedType[] ptypes = expr.constructor().parameters();
//
//		if(args != null){
//			for (int i = 0; i < args.length; i++) {
//
//				CType actualType = ptypes[i].staticType();
//				typeStr = typeStr + TransUtils.typeToClass(actualType);
//
//				LOG(" --> " + args[i].getClass().toString());
//				args[i].accept(this);
//				argsStr = argsStr + TransUtils.wrappedValue(actualType, (String) GET_RESULT());
//
//				if (i < args.length - 1) {
//					argsStr = argsStr + ", ";
//					typeStr = typeStr + ", ";
//				}
//			}
//		}
//		argsStr = argsStr + " }";
//		typeStr = typeStr + " }";
//
//		// target class of dynamic call
//		CClass clazz = ((CClassType) expr.getType()).getCClass();
//		// cn, fully qualified name of the target class
//		String cn = TransUtils.dynamicCallName(clazz);
//		// mn, the name of spec_public accessor method
//		String mn = isSpecPublic ?
//				"\"" +TransUtils.specPublicAccessorName(MN_INIT) +"\"" : null;
//
//				String result = 
//					TransUtils.unwrapObject(
//							expr.getApparentType(), "rac$invoke(\"" + cn + "\", " +	receiver+ ", " + mn + ", " + typeStr + ", " + argsStr + ")"
//					);
//
//				//LOG("!@! TEMP DEBUG !@! - translateToStaticNewObjectExpression : " + result);
//				RETURN_RESULT(result);
//	}	


	/**
	 * Translates an object allocator expression for an anonymous class.
	 */
	public void visitNewAnonymousClassExpression( 
			JNewAnonymousClassExpression self ) 
	{
		// throw(new NotImplementedExpressionException(self.getTokenReference(), "visitNewAnonymousClassExpression"));

		// !FIXME!
		String var = varGen.freshVar();
		CType type = self.getApparentType();
		/*	    
		RacNode quantifierEvaluation = RacParser.parseStatement(TransUtils.toString(type) + " " + var + " = " + TransUtils.defaultValue(type) + " ;\n$0\nreturn " + var + ";", node);
	    quantifierEvaluation = RacParser.parseStatement("JMLRacExpressionEvaluator " + var + "Evaluator = new JMLRacExpressionEvaluator(){public boolean eval(){\n$0\n}};", quantifierEvaluation);
		quantifiedStatementsStack.push(quantifierEvaluation);
		RETURN_RESULT(var + "Evaluator.eval()");
		 */	    

		prebuiltStatementsStack.push(RacParser.parseStatement(TransUtils.toString(type) + " " + var + " = $0 ;", self));

//		RETURN_RESULT(var);

//		// !FIXME! translate self? oh, no...
//		RacNode result = RacParser.parseStatement(
//		GET_ARGUMENT() + " = $0;", self);
//		RETURN_RESULT(result);
	}

	/**
	 * Translates an array allocator expression.
	 */
	public void visitNewArrayExpression( JNewArrayExpression self ) 
	{
		//throw(new NotImplementedExpressionException(self.getTokenReference(), "JNewArrayExpression"));

		String inits = "";
		JArrayDimsAndInits jArrayDimsAndInits = self.dims();
		if(jArrayDimsAndInits != null){
			JArrayInitializer jArrayInitializer = jArrayDimsAndInits.init();
			if(jArrayInitializer != null){
				JExpression[] elems = jArrayInitializer.elems();
				if(elems != null){
					inits = "{";
					for (int i = 0; i < elems.length; i++) {
						LOG(" --> " + elems[i].getClass().toString());
						elems[i].accept(this);
						inits = inits + GET_RESULT();
						if (i < elems.length - 1) {
							inits = inits + ", ";
						}
					}
					inits = inits + "}";
				}
			}
		}

		String result = "(new " + TransUtils.toString(self.getType()) + inits + ")";

		RETURN_RESULT(result);

		//new type[...]

//		// !FIXME! translate self, i.e., dims and initializer
//		RacNode result = RacParser.parseStatement(
//		GET_ARGUMENT() + " = $0;", self);
//		RETURN_RESULT(result);
	}

	public void visitArrayDimsAndInit( JArrayDimsAndInits self ) {
		// TODO - not implemented in the original RAC
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JArrayDimsAndInits"));
	}

	public void visitArrayInitializer( JArrayInitializer self ) {
		// TODO - not implemented in the original RAC
		throw(new NotImplementedExpressionException(self.getTokenReference(), "JArrayInitializer"));
	}


	// ----------------------------------------------------------------------
	// LITERALS
	// ----------------------------------------------------------------------

	/**
	 * Translates a boolean literal.
	 */
	public void visitBooleanLiteral(JBooleanLiteral self) {
		RETURN_RESULT(self.booleanValue() ? "true" : "false");
	}

	/**
	 * Translates a character literal.
	 */
	public void visitCharLiteral(JCharLiteral self) {
		RETURN_RESULT(self.image()); // !FIXME!
	}

	/**
	 * Translates an ordinal literal.
	 */
	public void visitOrdinalLiteral(JOrdinalLiteral self) {
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
			// !FIXME! ? will this do?
			visitBigintLiteral(value.longValue());
		} else {
			fail();
		}
	}

	/**
	 * Translates a byte literal.
	 */
	protected void visitByteLiteral(byte value) {
		RETURN_RESULT("(byte)" + value);
	}

	/**
	 * Translates a int literal.
	 */
	protected void visitIntLiteral(int value) {
		RETURN_RESULT(value + ""); // !FIXME!
	}

	/**
	 * Translates a long literal.
	 */
	protected void visitLongLiteral(long value) {
		RETURN_RESULT(value + "L");
	}

	/**
	 * Translates a \bigint literal.
	 */
	protected void visitBigintLiteral(long value) {
		RETURN_RESULT("java.math.BigInteger.valueOf(" + value + "L)");
	}

	/**
	 * Translates a short literal.
	 */
	protected void visitShortLiteral(short value) {
		RETURN_RESULT("(short)" + value);
	}

	/**
	 * Translates a real literal.
	 */
	public void visitRealLiteral(JRealLiteral self) {
		Number value = self.numberValue();
		CType type = self.getApparentType();
		assertTrue(value != null);

		if (type == CStdType.Double) {
			visitDoubleLiteral(value.doubleValue());
		} else if (type == CStdType.Float) {
			visitFloatLiteral(value.floatValue());
		} else if (type == JmlStdType.Real) {
			// !FIXME! ? will this do?
			visitDoubleLiteral(value.doubleValue());
		} else {
			fail();
		}
	}

	/**
	 * Translates a double literal.
	 */
	protected void visitDoubleLiteral(double value) {
		RETURN_RESULT(TransUtils.toString(value));
	}

	/**
	 * Translates a float literal.
	 */
	protected void visitFloatLiteral(float value) {
		RETURN_RESULT(TransUtils.toString(value));
	}

	/**
	 * Translates a string literal.
	 */
	public void visitStringLiteral(JStringLiteral self) {
		// !FIXME! unicode handling
		String value = self.stringValue();
		StringBuffer s = new StringBuffer();
		for (int i = 0; i < value.length(); i++) {
			char c = value.charAt(i);
			switch (c) {
			case '\n':
				s.append("\\n");
				break;
			case '\r':
				s.append("\\r");
				break;
			case '\t':
				s.append("\\t");
				break;
			case '\b':
				s.append("\\b");
				break;
			case '\f':
				s.append("\\f");
				break;
			case '\"':
				s.append("\\\"");
				break;
			case '\'':
				s.append("\\\'");
				break;
			case '\\':
				s.append("\\\\");
				break;
			default:
				s.append(c);
			}
		}
		value = s.toString();

		RETURN_RESULT('"' + value + '"');
	}

	/**
	 * Translates a null literal.
	 */
	public void visitNullLiteral(JNullLiteral self) {
		RETURN_RESULT("null");
	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/**
	 * Returns the top element of the result stack.
	 */
	public String GET_RESULT() {   
		return resultingExpression;
	}

	/**
	 * Puts the given object to the result stack. I.e., simulates returning of
	 * visitor method calls (to the calling visitor method).
	 */
	protected void RETURN_RESULT(String str) {
		//LOG("RESULT = " + str);
		resultingExpression = str;
	}

	/**
	 * Used for debugging pruposes only.
	 */
	protected void LOG(String str) {
		//System.out.println(str);
	}

	protected static void notExecutableClauseWarn(TokenReference tok, String description){
		JmlRacGenerator.warn(tok, RacMessages.NOT_EXECUTABLE, "Entire clause will be dropped since " + description);
	}

	protected static void notImplementedClauseFail(TokenReference tok, String description){
		notSupportedClauseFail(tok, description + " (not implemented yet)");
	}

	protected static void notSupportedClauseFail(TokenReference tok, String description){
		JmlRacGenerator.warn(tok, RacMessages.NOT_SUPPORTED_ALT, description);
	} 

	public boolean isProperlyEvaluated(){ return properlyEvaluated; }

	public void setEvaluatorPUse(String str){
		if(str == null)
			evaluatorPUse = "";
		else
			evaluatorPUse = str;
	};

	public void setEvaluatorPDef(String str){
		if(str == null)
			evaluatorPDef = "";
		else
			evaluatorPDef = str;
	};

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/**
	 * Generator of unique variable names.
	 */
	protected VarGenerator varGen;

	/**
	 * Variable to hold the reslt of the target expression.
	 */
	protected String resultVar;

	/**
	 * String containing visitor methods results.
	 */
	private String resultingExpression;


//	TODO: Do I really need this?
	/**
	 * Current translation context.
	 */
	protected RacContext context;

	/**
	 * Expression to translate.
	 */
	protected JExpression expression;

	// TODO: Do I really need this?
	/**
	 * The type declaration within which this expression resides (the type of
	 * 'this').
	 */
	protected JTypeDeclarationType typeDecl;

	//TODO: Do I really need this?
	/**
	 * Is the expression already translated?
	 */
	private boolean translated = false;

	protected /*@non_null@*/ String errorType;

	private boolean properlyEvaluated = false;
	protected PositionnedExpressionException reportedException = null;

	/**
	 * Keep track of this translator is helping a translator translate
	 * an inner class
	 */
	protected boolean isInner = false;	

	/**
	 * Contains node that were translated using helpers. They are to be appended
	 * before the actual expressions's translation 
	 */
	protected Stack prebuiltStatementsStack = new Stack();

	protected String evaluatorPUse = "";
	protected String evaluatorPDef = "";

	//to manage scope with inner anonymous class
	protected String thisIs = "";
	
	private StringBuffer tokenReference = null;

}
