/*
 * Copyright (C) 2008-2013 Federal University of Pernambuco and 
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
 * $Id: ConstraintMethodClientAwareChecking.java,v 1.0 2010/04/02 13:53:09 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.jmlspecs.checker.JmlClassDeclaration;
import org.jmlspecs.checker.JmlConstraint;
import org.jmlspecs.checker.JmlMethodName;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JMethodDeclarationType;

/**
 * A class for generating assertion check methods for (history)
 * constraints.  There are two types of history constraints:
 * <em>instance</em> (<em>non-static</em>) <em>constraints</em> and
 * <em>class</em> (<em>static</em>) <em>constraints</em>.  As thus,
 * two types of constraint check methods are generated.  An instance
 * constraint method checks both the instance and class constraints
 * while a class constraint method checks only the class constraints.
 * The generated constraint check methods inherit its superclass's
 * constraints by dynamically invoking the corresponding assertion
 * methods.  The inheritance of history constrains is interpreted
 * differently between <em>strong</em> and <em>weak</em> behavioral
 * subtyping.  For strong behavioral subtyping, the suptype's history
 * constraints are inherited by all methods of the subtype, while for
 * weak behavior subtyping, the supertype's constraints are inhertied
 * only by overriding methods of the subtype.
 *
 * <p>
 * The class implements a variant of the <em>Template Pattern</em>
 * [GoF95], prescribed in the class {@link AssertionMethod}.
 * </p>
 *
 * @see AssertionMethod
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */

public class ConstraintMethodClientAwareChecking extends AssertionMethod {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/** Construct a new instance.
	 *
	 * @param isStatic the kind of constraint method to generate;
	 *                 <code>true</code> for static and <code>false</code> 
	 *                 for non-static (instance) constraint method.
	 * @param typeDecl the target type declaration whose constraint methods
	 *                 are to be generated.
	 */
	protected ConstraintMethodClientAwareChecking(boolean isStatic, 
			/*@ non_null @*/ JmlTypeDeclaration typeDecl, VarGenerator varGen) {
		this.exceptionToThrow = "JMLHistoryConstraintError";
		this.typeDecl = typeDecl;
		this.varGen = varGen;
		
		this.oldExprs = new ArrayList();
		this.oldExprsDecl = new ArrayList();
		this.oldExprsForStat = new ArrayList();
		this.oldExprsDeclForStat = new ArrayList();
		this.publicOldExprs = new ArrayList();
		this.publicOldExprsDecl = new ArrayList();
		this.publicOldExprsForStat = new ArrayList();
		this.publicOldExprsDeclForStat = new ArrayList();
		this.protectedOldExprs = new ArrayList();
		this.protectedOldExprsDecl = new ArrayList();
		this.protectedOldExprsForStat = new ArrayList();
		this.protectedOldExprsDeclForStat = new ArrayList();
		this.defaultOldExprs = new ArrayList();
		this.defaultOldExprsDecl = new ArrayList();
		this.defaultOldExprsForStat = new ArrayList();
		this.defaultOldExprsDeclForStat = new ArrayList();
		this.privateOldExprs = new ArrayList();
		this.privateOldExprsDecl = new ArrayList();
		this.privateOldExprsForStat = new ArrayList();
		this.privateOldExprsDeclForStat = new ArrayList();
		
		this.publicInstConstPred = AspectUtil.changeThisOrSuperRefToAdviceRef(combineUniversalConstraints(false, this.varGen, ACC_PUBLIC), typeDecl);
		this.publicStatConstPred = combineUniversalConstraints(true, this.varGen, ACC_PUBLIC);
		this.hasPublicInstConst = !this.publicInstConstPred.equals("");
		this.hasPublicStatConst = !this.publicStatConstPred.equals("");
		
		this.protectedInstConstPred = AspectUtil.changeThisOrSuperRefToAdviceRef(combineUniversalConstraints(false, this.varGen, ACC_PROTECTED), typeDecl);
		this.protectedStatConstPred = combineUniversalConstraints(true, this.varGen, ACC_PROTECTED);
		this.hasProtectedInstConst = !this.protectedInstConstPred.equals("");
		this.hasProtectedStatConst = !this.protectedStatConstPred.equals("");
		
		this.defaultInstConstPred = AspectUtil.changeThisOrSuperRefToAdviceRef(combineUniversalConstraints(false, this.varGen, 0L), typeDecl);
		this.defaultStatConstPred = combineUniversalConstraints(true, this.varGen, 0L);
		this.hasDefaultInstConst = !this.defaultInstConstPred.equals("");
		this.hasDefaultStatConst = !this.defaultStatConstPred.equals("");
		
		this.privateInstConstPred = AspectUtil.changeThisOrSuperRefToAdviceRef(combineUniversalConstraints(false, this.varGen, ACC_PRIVATE), typeDecl);
		this.privateStatConstPred = combineUniversalConstraints(true, this.varGen, ACC_PRIVATE);
		this.hasPrivateInstConst = !this.privateInstConstPred.equals("");
		this.hasPrivateStatConst = !this.privateStatConstPred.equals("");

		// javadoc to be added to the generated constraint method
		this.javadoc = "/** Generated by AspectJML to check " + 
		"non-static" + " constraints of \n" + 
		((typeDecl instanceof JmlClassDeclaration) ? 
				" * class " : " * interface ") +
				typeDecl.ident() + ". */";

		this.javadocStat = "/** Generated by AspectJML to check " + 
		"static"  + " constraints of \n" + 
		((typeDecl instanceof JmlClassDeclaration) ? 
				" * class " : " * interface ") +
				typeDecl.ident() + ". */";
	}

	// ----------------------------------------------------------------------
	// GENERATION
	// ----------------------------------------------------------------------

	public JMethodDeclarationType generate(RacNode stmt)
	{
		return null;
	}

	public JMethodDeclarationType generate()
	{
		StringBuffer code = buildAroundAdvice();
		code.append("\n");

		return RacParser.parseMethod(code.toString(), null);
	}

	/** Builds and returns the method header of the assertion check
	 * method as a string.
	 * 
	 */
	protected StringBuffer buildAroundAdvice() 
	{
		// By Henrique Rebelo
		String classQualifiedName = AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName());		
		String packageQualifiedName = this.typeDecl.getCClass().getJavaName().replace(this.typeDecl.ident(), "");
		final StringBuffer code = new StringBuffer();
		final String HEADER = "@post <File \\\""+this.typeDecl.ident()+".java\\\">";
		
		String errorMsgForPublicInstConst = "\"";
		String errorMsgForPublicStatConst = "\"";
		String errorMsgForProtectedInstConst = "\"";
		String errorMsgForProtectedStatConst = "\"";
		String errorMsgForDefaultInstConst = "\"";
		String errorMsgForDefaultStatConst = "\"";
		String errorMsgForPrivateInstConst = "\"";
		String errorMsgForPrivateStatConst = "\"";
		String evalErrorMsgForPublicInstConst = "\"";
		String evalErrorMsgForPublicStatConst = "\"";
		String evalErrorMsgForProtectedInstConst = "\"";
		String evalErrorMsgForProtectedStatConst = "\"";
		String evalErrorMsgForDefaultInstConst = "\"";
		String evalErrorMsgForDefaultStatConst = "\"";
		String evalErrorMsgForPrivateInstConst = "\"";
		String evalErrorMsgForPrivateStatConst = "\"";

		if (!this.getConstraintTokenReference(false).equals("")){
			// JML Constraint Error
			errorMsgForPublicInstConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPublicInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PUBLIC);
			errorMsgForPublicInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PUBLIC);
			
			errorMsgForProtectedInstConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForProtectedInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PROTECTED);
			errorMsgForProtectedInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PROTECTED);
			
			errorMsgForDefaultInstConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForDefaultInstConst += ", " + this.getVisibilityConstraintTokenReference(false, 0L);
			errorMsgForDefaultInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, 0L);
			
			errorMsgForPrivateInstConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPrivateInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PRIVATE);
			errorMsgForPrivateInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PRIVATE);

			// JML Evaluation Error
			evalErrorMsgForPublicInstConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPublicInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PUBLIC);
			evalErrorMsgForPublicInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PUBLIC);
			
			evalErrorMsgForProtectedInstConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForProtectedInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PROTECTED);
			evalErrorMsgForProtectedInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PROTECTED);
			
			evalErrorMsgForDefaultInstConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForDefaultInstConst += ", " + this.getVisibilityConstraintTokenReference(false, 0L);
			evalErrorMsgForDefaultInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, 0L);
			
			evalErrorMsgForPrivateInstConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPrivateInstConst += ", " + this.getVisibilityConstraintTokenReference(false, ACC_PRIVATE);
			evalErrorMsgForPrivateInstConst += this.getVisibilityContextValuesForConstraint(false, this.varGen, ACC_PRIVATE);
		}

		if (!this.getConstraintTokenReference(true).equals("")){
			// JML Constraint Error
			errorMsgForPublicStatConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPublicStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PUBLIC);
			errorMsgForPublicStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PUBLIC);
			
			errorMsgForProtectedStatConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForProtectedStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PROTECTED);
			errorMsgForProtectedStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PROTECTED);
			
			errorMsgForDefaultStatConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForDefaultStatConst += ", " + this.getVisibilityConstraintTokenReference(true, 0L);
			errorMsgForDefaultStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, 0L);
			
			errorMsgForPrivateStatConst = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPrivateStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PRIVATE);
			errorMsgForPrivateStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PRIVATE);

			// JML Evaluation Error
			evalErrorMsgForPublicStatConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPublicStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PUBLIC);
			evalErrorMsgForPublicStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PUBLIC);
			
			evalErrorMsgForProtectedStatConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForProtectedStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PROTECTED);
			evalErrorMsgForProtectedStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PROTECTED);
			
			evalErrorMsgForDefaultStatConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForDefaultStatConst += ", " + this.getVisibilityConstraintTokenReference(true, 0L);
			evalErrorMsgForDefaultStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, 0L);
			
			evalErrorMsgForPrivateStatConst = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPrivateStatConst += ", " + this.getVisibilityConstraintTokenReference(true, ACC_PRIVATE);
			evalErrorMsgForPrivateStatConst += this.getVisibilityContextValuesForConstraint(true, this.varGen, ACC_PRIVATE);
		}

		//Rebelo - Only generate constraint checking method if there are constraints
		// Translating universal constraints

		// handling universal constraints
		if((this.hasPublicInstConst) && (this.hasPublicStatConst)) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "public constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPublicInstConst, evalErrorMsgForPublicInstConst,
					this.publicInstConstPred, hasPublicOldExpressions, publicOldExprsDecl, publicOldExprs, false, ACC_PUBLIC);
			code.append("\n");
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "public constraints"));
			code.append("\n"); 
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPublicStatConst, evalErrorMsgForPublicStatConst,
					this.publicStatConstPred, hasPublicOldExpressionsForStat, publicOldExprsDeclForStat, publicOldExprsForStat, true, ACC_PUBLIC);
		}
		else if(this.hasPublicInstConst) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "public constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPublicInstConst, evalErrorMsgForPublicInstConst,
					this.publicInstConstPred, hasPublicOldExpressions, publicOldExprsDecl, publicOldExprs, false, ACC_PUBLIC);
		}
		else if(this.hasPublicStatConst){
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "public constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPublicStatConst, evalErrorMsgForPublicStatConst,
					this.publicStatConstPred, hasPublicOldExpressionsForStat, publicOldExprsDeclForStat, publicOldExprsForStat, true, ACC_PUBLIC);
		}

		if((this.hasProtectedInstConst) && (this.hasProtectedStatConst)) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "protected constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForProtectedInstConst, evalErrorMsgForProtectedInstConst,
					this.protectedInstConstPred, hasProtectedOldExpressions, protectedOldExprsDecl, protectedOldExprs, false, ACC_PROTECTED);
			code.append("\n");
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "protected constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForProtectedStatConst, evalErrorMsgForProtectedStatConst,
					this.protectedStatConstPred, hasProtectedOldExpressionsForStat, protectedOldExprsDeclForStat, protectedOldExprsForStat, true, ACC_PROTECTED);
		}
		else if(this.hasProtectedInstConst) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "protected constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForProtectedInstConst, evalErrorMsgForProtectedInstConst,
					this.protectedInstConstPred, hasProtectedOldExpressions, protectedOldExprsDecl, protectedOldExprs, false, ACC_PROTECTED);
		}
		else if(this.hasProtectedStatConst){
			code.append("\n");
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "protected constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForProtectedStatConst, evalErrorMsgForProtectedStatConst,
					this.protectedStatConstPred, hasProtectedOldExpressionsForStat, protectedOldExprsDeclForStat, protectedOldExprsForStat, true, ACC_PROTECTED);
		}
		
		if((this.hasDefaultInstConst) && (this.hasDefaultStatConst)) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "default constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForDefaultInstConst, evalErrorMsgForDefaultInstConst,
					this.defaultInstConstPred, hasDefaultOldExpressions, defaultOldExprsDecl, defaultOldExprs, false, 0L);
			code.append("\n");
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "default constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForDefaultStatConst, evalErrorMsgForDefaultStatConst,
					this.defaultStatConstPred, hasDefaultOldExpressionsForStat, defaultOldExprsDeclForStat, defaultOldExprsForStat, true, 0L);
		}
		else if(this.hasDefaultInstConst) { 
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "default constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForDefaultInstConst, evalErrorMsgForDefaultInstConst,
					this.defaultInstConstPred, hasDefaultOldExpressions, defaultOldExprsDecl, defaultOldExprs, false, 0L);
		}
		else if(this.hasDefaultStatConst){
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", " default constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForDefaultStatConst, evalErrorMsgForDefaultStatConst,
					this.defaultStatConstPred, hasDefaultOldExpressionsForStat, defaultOldExprsDeclForStat, defaultOldExprsForStat, true, 0L);
		}
		
		if((this.hasPrivateInstConst) && (this.hasPrivateStatConst)) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "private constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPrivateInstConst, evalErrorMsgForPrivateInstConst,
					this.privateInstConstPred, hasPrivateOldExpressions, privateOldExprsDecl, privateOldExprs, false, ACC_PRIVATE);
			code.append("\n");
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "private constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPrivateStatConst, evalErrorMsgForPrivateStatConst,
					this.privateStatConstPred, hasPrivateOldExpressionsForStat, privateOldExprsDeclForStat, privateOldExprsForStat, true, ACC_PRIVATE);
		}
		else if(this.hasPrivateInstConst) {
			code.append("\n"); 
			code.append(this.javadoc.replace("constraints", "private constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPrivateInstConst, evalErrorMsgForPrivateInstConst,
					this.privateInstConstPred, hasPrivateOldExpressions, privateOldExprsDecl, privateOldExprs, false, ACC_PRIVATE);
		}
		else if(this.hasPrivateStatConst){
			code.append("\n");
			code.append(this.javadocStat.replace("constraints", "private constraints"));
			code.append("\n");
			this.generateAroundAdviceForUniversalConstraintChecking(
					classQualifiedName, packageQualifiedName, code,
					errorMsgForPrivateStatConst, evalErrorMsgForPrivateStatConst,
					this.privateStatConstPred, hasPrivateOldExpressionsForStat, privateOldExprsDeclForStat, privateOldExprsForStat, true, ACC_PRIVATE);
		}
			
		// Translating specific constraints
		String specPublicInstConst =  this.generateVisibilityCodeForSpecificConstraintChecking(false, this.varGen, ACC_PUBLIC);
		String specPublicStatConst =  this.generateVisibilityCodeForSpecificConstraintChecking(true, this.varGen, ACC_PUBLIC);
		
		String specProtectedInstConst =  this.generateVisibilityCodeForSpecificConstraintChecking(false, this.varGen, ACC_PROTECTED);
		String specProtectedStatConst =  this.generateVisibilityCodeForSpecificConstraintChecking(true, this.varGen, ACC_PROTECTED);
		
		String specDefaultInstConst =  this.generateVisibilityCodeForSpecificConstraintChecking(false, this.varGen, 0L);
		String specDefaultStatConst =  this.generateVisibilityCodeForSpecificConstraintChecking(true, this.varGen, 0L);
		
		String specPrivateInstConst =  this.generateVisibilityCodeForSpecificConstraintChecking(false, this.varGen, ACC_PRIVATE);
		String specPrivateStatConst =  this.generateVisibilityCodeForSpecificConstraintChecking(true, this.varGen, ACC_PRIVATE);

		if((this.hasInstConst) || (this.hasStatConst)){
			code.append("\n");
		}

		if(!(specPublicInstConst.equals("")) && (!specPublicStatConst.equals(""))){
			code.append(specPublicInstConst);
			code.append("\n");
			code.append(specPublicStatConst);
		}
		else if (!specPublicInstConst.equals("")){
			code.append(specPublicInstConst);
		}
		else if (!specPublicStatConst.equals("")){
			code.append(specPublicStatConst);
		}
		
		if(!(specProtectedInstConst.equals("")) && (!specProtectedStatConst.equals(""))){
			code.append(specProtectedInstConst);
			code.append("\n");
			code.append(specProtectedStatConst);
		}
		else if (!specProtectedInstConst.equals("")){
			code.append(specProtectedInstConst);
		}
		else if (!specProtectedStatConst.equals("")){
			code.append(specProtectedStatConst);
		}
		
		if(!(specDefaultInstConst.equals("")) && (!specDefaultStatConst.equals(""))){
			code.append(specDefaultInstConst);
			code.append("\n");
			code.append(specDefaultStatConst);
		}
		else if (!specDefaultInstConst.equals("")){
			code.append(specDefaultInstConst);
		}
		else if (!specDefaultStatConst.equals("")){
			code.append(specDefaultStatConst);
		}
		
		if(!(specPrivateInstConst.equals("")) && (!specPrivateStatConst.equals(""))){
			code.append(specPrivateInstConst);
			code.append("\n");
			code.append(specPrivateStatConst);
		}
		else if (!specPrivateInstConst.equals("")){
			code.append(specPrivateInstConst);
		}
		else if (!specPrivateStatConst.equals("")){
			code.append(specPrivateStatConst);
		}
		
		return code;
	}

	/**
	 * @param classQualifiedName
	 * @param code
	 * @param errorMsg
	 * @param evalErrorMsg
	 */
	private void generateAroundAdviceForUniversalConstraintChecking(
			String classQualifiedName, String packageQualifiedName, final StringBuffer code,
			String errorMsg, String evalErrorMsg, String constPred, boolean hasOldExpressions, List oldExprsDecl, List oldExprs, boolean forStatic, long visibility) {
		
		String adviceexecution = "";
		if(AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)){
			adviceexecution = " || (adviceexecution())";
		}
	
		if (visibility == ACC_PUBLIC) {
			this.exceptionToThrow = "JMLHistoryConstraintError";
		} else if (visibility == ACC_PROTECTED) {
			this.exceptionToThrow = "JMLProtectedHistoryConstraintError";
		} else if (visibility == 0L) { //default
			this.exceptionToThrow = "JMLDefaultHistoryConstraintError";
		} else if (visibility == ACC_PRIVATE) {
			this.exceptionToThrow = "JMLPrivateHistoryConstraintError";
		}
		
		if(forStatic){
			code.append("Object around (");	
			code.append(")").append(" :");
		}
		else{
			code.append("Object around (final ").append(classQualifiedName).append(" ").append("object$rac");	
			code.append(")").append(" :");	
		}
		code.append("\n");
		// making static constraints inheritable to be checked on subtypes - hemr
		if(forStatic){
			code.append("   (call(* "+classQualifiedName+"+.*(..))");
			code.append(" || ");
			code.append("\n");	
			code.append("   call("+classQualifiedName+"+.new(..))").append(adviceexecution).append(")");
			code.append(" && ");
			code.append("\n");	
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append("   !@annotation(JMLHelper)");
				code.append(" && ");
				code.append("\n");	
			}
		}
		else{
			code.append("   (call(!static * "+classQualifiedName+"+.*(..))").append(" && \n");	
			code.append("     !call(void "+classQualifiedName+".finalize() throws Throwable)").append(adviceexecution).append(")");
			code.append(" && ");
			code.append("\n");	
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append("   !@annotation(JMLHelper)");
				code.append(" && ");
			}
		}
		if(visibility == ACC_PROTECTED){
			code.append("   (within("+(packageQualifiedName.equals("")?"":packageQualifiedName)+"*) || within("+classQualifiedName+"+))").append(" && ");
			
			code.append("\n");	
		}
		else if(visibility == 0L){//package
			code.append("   within("+(packageQualifiedName.equals("")?"":packageQualifiedName)+"*)").append(" && ");
			code.append("\n");	
		}
		else if(visibility == ACC_PRIVATE){
			code.append("   within("+classQualifiedName+")").append(" && ");
			code.append("\n");	
		}
		if(!forStatic){
			code.append("   target(object$rac)");
			code.append(" && ");
			code.append("\n");
		}
		code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
		code.append(" {\n");
		
		code.append("    ").append("Object").append(" ").append("rac$result");
		code.append(" = ").append("null").append(";\n");
		if(hasOldExpressions){
			for (Iterator iterator = oldExprsDecl.iterator(); iterator.hasNext();) {
				String currentOldExprsDecl = (String) iterator.next();
				code.append("    final "+currentOldExprsDecl);
				code.append("\n");
			}
		}
		if(hasOldExpressions){
			code.append("    try {\n");
			code.append("      // saving all old values");
			code.append("\n");

			for (Iterator iterator = oldExprs.iterator(); iterator.hasNext();) {
				String currentOldExpr = (String) iterator.next();
				if(forStatic){
					code.append("\t\t"+currentOldExpr);
				}
				else{
					code.append("\t\t"+AspectUtil.changeThisOrSuperRefToAdviceRef(currentOldExpr, typeDecl));
				}
				code.append("\n");
			}

			code.append("     } catch (Throwable rac$cause) {\n");
			code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
			code.append("     }");
			code.append("\n");
			
		}
		code.append("    boolean rac$b = true;\n");
		code.append("    try {\n");
		if(forStatic){
			code.append("      ").append("rac$result = proceed()").append(";").append("//calling the method\n");	
		}
		else{
			code.append("      ").append("rac$result = proceed(object$rac)").append(";").append("//calling the method\n");	
		}		
		// adding JML quantifierInnerClasses if any
		code.append(this.getQuantifierInnerClasses(constPred));
		code.append("      try {\n");
		code.append("       rac$b = "+constPred+";\n");
		code.append("      } catch (JMLNonExecutableException rac$nonExec) {\n");
		code.append("         rac$b = ").append(Main.aRacOptions.mustBeExecutable()).append(";\n");
		code.append("      } catch (Throwable rac$cause) {\n");
		code.append("        if(rac$cause instanceof JMLAssertionError) {\n");
		code.append("          throw (JMLAssertionError) rac$cause;\n");
		code.append("        }\n");
		code.append("        else {\n");
		code.append("          throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("        }\n");
		code.append("      }\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("      JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", "+visibility+");");
		}
		else{
			code.append("      JMLChecker.checkConstraint(rac$b, \""+errorMsg+", "+visibility+");");
		}
		code.append("\n").append("    ").append(" }");
		code.append(" catch (Throwable rac$e) {\n");
		code.append("         if(rac$e instanceof JMLEvaluationError){\n");
		code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$e);\n");
		code.append("         }\n");
		code.append("         JMLChecker.rethrowJMLAssertionError(rac$e, \"\");\n");
		code.append("         rac$b = true;\n");
		code.append("         try ");
		code.append(" {\n");
		// adding JML quantifierInnerClasses if any
		code.append(this.getQuantifierInnerClasses(constPred));
		code.append("           try {\n");
		code.append("            rac$b = "+constPred+";\n");
		code.append("           } catch (JMLNonExecutableException rac$nonExec) {\n");
		code.append("             rac$b = ").append(Main.aRacOptions.mustBeExecutable()).append(";\n");
		code.append("           } catch (Throwable rac$cause) {\n");
		code.append("             if(rac$cause instanceof JMLAssertionError) {\n");
		code.append("              throw (JMLAssertionError) rac$cause;\n");
		code.append("           }\n");
		code.append("             else {\n");
		code.append("              throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("             }\n");
		code.append("           }\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("           JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", "+visibility+");");
		}
		else{
			code.append("           JMLChecker.checkConstraint(rac$b, \""+errorMsg+", "+visibility+");");
		}
		code.append("         } catch (Throwable rac$cause)");
		code.append(" {\n");
		code.append("             if (rac$cause instanceof JMLHistoryConstraintError) {\n");
		code.append("               throw (JMLHistoryConstraintError) rac$e;\n");
		code.append("             }\n");
		code.append("             else {\n");
		code.append("               throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$e);\n");
		code.append("             }");
		code.append("\n").append("         ").append("}");
		code.append("\n").append("        }");
		code.append("\n");
		code.append("    ").append("return rac$result;");
		code.append("\n").append("   }");
	}

	private void generateAroundAdviceForSpecificConstraintChecking(
			String classQualifiedName, String packageQualifiedName, final StringBuffer code,
			String errorMsg, String evalErrorMsg, String constPred, String [] methodNames, boolean forStatic, long visibility) {

		if (visibility == ACC_PUBLIC) {
			this.exceptionToThrow = "JMLHistoryConstraintError";
		} else if (visibility == ACC_PROTECTED) {
			this.exceptionToThrow = "JMLProtectedHistoryConstraintError";
		} else if (visibility == 0L) { //default
			this.exceptionToThrow = "JMLDefaultHistoryConstraintError";
		} else if (visibility == ACC_PRIVATE) {
			this.exceptionToThrow = "JMLPrivateHistoryConstraintError";
		}
		
		if(forStatic){
			code.append("Object around (");	
			code.append(")").append(" :");
		}
		else{
			code.append("Object around (final ").append(classQualifiedName).append(" ").append("object$rac");	
			code.append(")").append(" :");	
		}
		code.append("\n");
		for (int i = 0; i < methodNames.length; i++) {
			if((i == 0) && (methodNames.length > 1)){
				  code.append((methodNames[i].contains("new")? "   (call("+classQualifiedName+"."+methodNames[i]+")" : "   (call(* "+classQualifiedName+"."+methodNames[i]+")"));
			}	
			else if((i == 0) && (methodNames.length == 1)){				
			  code.append((methodNames[i].contains("new")? "   call("+classQualifiedName+"."+methodNames[i]+")" : "   call(* "+classQualifiedName+"."+methodNames[i]+")"));
			}
			else {
				code.append(" || ");
				code.append("\n");
				code.append((methodNames[i].contains("new")? "   call("+classQualifiedName+"."+methodNames[i]+")" : "   call(* "+classQualifiedName+"."+methodNames[i]+")"));	
			}
			if((i == (methodNames.length-1)) && (methodNames.length > 1)){
				  code.append(")");
			}	  
		}
		code.append(" && ");
		code.append("\n");
		if(visibility == ACC_PROTECTED){
			code.append("   (within("+(packageQualifiedName.equals("")?"":packageQualifiedName)+"*) || within("+classQualifiedName+"+))").append(" && ");
			code.append("\n");	
		}
		else if(visibility == 0L){//package
			code.append("   within("+(packageQualifiedName.equals("")?"":packageQualifiedName)+"*)").append(" && ");
			code.append("\n");	
		}
		else if(visibility == ACC_PRIVATE){
			code.append("   within("+classQualifiedName+")").append(" && ");
			code.append("\n");	
		}
		if(!forStatic){
			code.append("   target(object$rac)");
			code.append(" && ");
			code.append("\n");
		}
		code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
		code.append(" {\n");
		code.append("    ").append("Object").append(" ").append("rac$result");
		code.append(" = ").append("null").append(";\n");
		if(forStatic){
			if(this.hasOldExpressionsForStat){
				for (Iterator iterator = oldExprsDeclForStat.iterator(); iterator.hasNext();) {
					String currentOldExprsDecl = (String) iterator.next();
					code.append("    final "+currentOldExprsDecl);
					code.append("\n");
				}
			}
			if(this.hasOldExpressionsForStat){
				code.append("    try {\n");
				code.append("      // saving all old values");
				code.append("\n");

				for (Iterator iterator = oldExprsForStat.iterator(); iterator.hasNext();) {
					String currentOldExpr = (String) iterator.next();
					code.append("\t\t"+currentOldExpr);
					code.append("\n");
				}

				code.append("     } catch (Throwable rac$cause) {\n");
				code.append("        if(rac$cause instanceof JMLAssertionError) {\n");
				code.append("          throw (JMLAssertionError) rac$cause;\n");
				code.append("        }\n");
				code.append("        else {\n");
				code.append("          throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
				code.append("        }\n");
				code.append("     }");
				code.append("\n");
			}	
		}
		else{
			if(this.hasOldExpressions){
				for (Iterator iterator = oldExprsDecl.iterator(); iterator.hasNext();) {
					String currentOldExprsDecl = (String) iterator.next();
					code.append("    final "+currentOldExprsDecl);
					code.append("\n");
				}
			}
			if(this.hasOldExpressions){
				code.append("    try {\n");
				code.append("      // saving all old values");
				code.append("\n");

				for (Iterator iterator = oldExprs.iterator(); iterator.hasNext();) {
					String currentOldExpr = (String) iterator.next();
					code.append("\t\t"+AspectUtil.changeThisOrSuperRefToAdviceRef(currentOldExpr, typeDecl));
					code.append("\n");
				}

				code.append("     } catch (Throwable rac$cause) {\n");
				code.append("        if(rac$cause instanceof JMLAssertionError) {\n");
				code.append("          throw (JMLAssertionError) rac$cause;\n");
				code.append("        }\n");
				code.append("        else {\n");
				code.append("          throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
				code.append("        }\n");
				code.append("     }");
				code.append("\n");
			}	
		}
		code.append("    boolean rac$b = true;\n");
		code.append("    try {\n");
		if(forStatic){
			code.append("      ").append("rac$result = proceed()").append(";").append("//calling the method\n");
		}
		else{
			code.append("      ").append("rac$result = proceed(object$rac)").append(";").append("//calling the method\n");	
		}	
		// adding JML quantifierInnerClasses if any
		code.append(this.getQuantifierInnerClasses(constPred));
		code.append("      rac$b = "+constPred+";\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("      JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", "+visibility+");");
		}
		else{
			code.append("      JMLChecker.checkConstraint(rac$b, \""+errorMsg+", "+visibility+");");
		}
		code.append("\n").append("    ").append(" }");
		code.append(" catch (Throwable rac$e) {\n");
		code.append("         if(rac$e instanceof JMLEvaluationError){\n");
		code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$e);\n");
		code.append("         }\n");
		code.append("         JMLChecker.rethrowJMLAssertionError(rac$e, \"\");\n");
		code.append("         rac$b = true;\n");
		code.append("         try ");
		code.append(" {\n");
		// adding JML quantifierInnerClasses if any
		code.append(this.getQuantifierInnerClasses(constPred));
		code.append("           rac$b = "+constPred+";\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("           JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", "+visibility+");");
		}
		else{
			code.append("           JMLChecker.checkConstraint(rac$b, \""+errorMsg+", "+visibility+");");
		}
		code.append("         } catch (Throwable rac$cause)");
		code.append(" {\n");
		code.append("             if (rac$cause instanceof JMLHistoryConstraintError) {\n");
		code.append("               throw (JMLHistoryConstraintError) rac$e;\n");
		code.append("             }\n");
		code.append("             else {\n");
		code.append("               throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$e);\n");
		code.append("             }");
		code.append("\n").append("         ").append("}");
		code.append("\n").append("       }");
		code.append("\n");
		code.append("    ").append("return rac$result;");
		code.append("\n").append("   }");
	}

	private String combineUniversalConstraints(boolean forStatic, VarGenerator varGen, long visibility){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		JmlConstraint [] constraints = typeDecl.constraints();
		
		for (int i = 0; i < constraints.length; i++) {
			// skip uncheckable constraints (e.g., redundant,
			// not requested, or trivially true.
			if (!isCheckable(constraints[i]))
				continue;

			// means that is not a public constraint
			if(privacy(constraints[i].modifiers()) != ACC_PUBLIC){
				TransPostExpression2 transInv = null;
				if (constraints[i].predicate() != null){
					transInv = 
							new TransPostExpression2(mvarGen, null, mvarGen, 
									false, 
									constraints[i].predicate(), null, this.typeDecl, "JMLInvariantError");
					// checking the missing rules for type specifications
					checkPrivacyRulesOKForTypeSpecs(transInv.stmtAsString(), privacy(constraints[i].modifiers()), constraints[i].getTokenReference());
				}
			}
		}
		
		// conjoin universal constraints while translating
		// non-universal (i.e., method-specific) ones separately
		JExpression left = null;
		for (int i = 0; i < constraints.length; i++) {
			// skip uncheckable constraints (e.g., redundant,
			// not requested, or trivially true.
			if (!isCheckable(constraints[i])
					|| (hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
					|| !(privacy(constraints[i].modifiers()) == visibility)){
				continue;
			}	

			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				continue;
			}

			// conjoin universal constraints
			JExpression p = new RacPredicate(constraints[i].predicate());
			left = left == null ? 
					p : new JConditionalAndExpression(org.multijava.util.compiler.TokenReference.NO_REF, left, p);

		}

		TransPostExpression2 transConstraint = null;
		if (left != null){
			transConstraint = 
				new TransPostExpression2(mvarGen, null, mvarGen, 
						false, 
						left, null, this.typeDecl, "JMLHistoryConstraintError");

			transConstraint.stmt(true); 

			// list of old expressions
			if(forStatic){
				if(visibility == ACC_PUBLIC){
					this.hasPublicOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
					this.publicOldExprsForStat.addAll(transConstraint.oldExprs());
					this.publicOldExprsDeclForStat.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == ACC_PROTECTED){
					this.hasProtectedOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
					this.protectedOldExprsForStat.addAll(transConstraint.oldExprs());
					this.protectedOldExprsDeclForStat.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == 0L){
					this.hasDefaultOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
					this.defaultOldExprsForStat.addAll(transConstraint.oldExprs());
					this.defaultOldExprsDeclForStat.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == ACC_PRIVATE){
					this.hasPrivateOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
					this.privateOldExprsForStat.addAll(transConstraint.oldExprs());
					this.privateOldExprsDeclForStat.addAll(transConstraint.oldVarDecl());
				}
			}
			else{
				if(visibility == ACC_PUBLIC){
					this.hasPublicOldExpressions = transConstraint.oldExprs().size() > 0;
					this.publicOldExprs.addAll(transConstraint.oldExprs());
					this.publicOldExprsDecl.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == ACC_PROTECTED){
					this.hasProtectedOldExpressions = transConstraint.oldExprs().size() > 0;
					this.protectedOldExprs.addAll(transConstraint.oldExprs());
					this.protectedOldExprsDecl.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == 0L){
					this.hasDefaultOldExpressions = transConstraint.oldExprs().size() > 0;
					this.defaultOldExprs.addAll(transConstraint.oldExprs());
					this.defaultOldExprsDecl.addAll(transConstraint.oldVarDecl());
				}
				else if(visibility == ACC_PRIVATE){
					this.hasPrivateOldExpressions = transConstraint.oldExprs().size() > 0;
					this.privateOldExprs.addAll(transConstraint.oldExprs());
					this.privateOldExprsDecl.addAll(transConstraint.oldVarDecl());
				}			
			}
			
			if(Main.aRacOptions.multipleSpecCaseChecking()){
				AspectUtil.getInstance().currentCompilationUnitHasConstraints();
			}

			return transConstraint.stmtAsString();
		}
		else{
			return "";	
		}
	}

	private String generateVisibilityCodeForSpecificConstraintChecking(boolean forStatic, VarGenerator varGen, long visibility){
		final StringBuffer code = new StringBuffer("");
		String classQualifiedName = this.typeDecl.getCClass().getJavaName();
		String packageQualifiedName = this.typeDecl.getCClass().getJavaName().replace(this.typeDecl.ident(), "");
		final String HEADER = "@post <File \\\""+this.typeDecl.ident()+".java\\\">";
		String errorMsg = "\"";
		String evalErrorMsg = "\"\"";
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		boolean isNotFirst = false;
		JmlConstraint [] constraints = typeDecl.constraints();
		
		for (int i = 0; i < constraints.length; i++) {
			// skip uncheckable constraints (e.g., redundant,
			// not requested, or trivially true.
			if (!isCheckable(constraints[i]))
				continue;

			// means that is not a public constraint
			if(privacy(constraints[i].modifiers()) != ACC_PUBLIC){
				TransPostExpression2 transInv = null;
				if (constraints[i].predicate() != null){
					transInv = 
							new TransPostExpression2(mvarGen, null, mvarGen, 
									false, 
									constraints[i].predicate(), null, this.typeDecl, "JMLInvariantError");
					// checking the missing rules for type specifications
					checkPrivacyRulesOKForTypeSpecs(transInv.stmtAsString(), privacy(constraints[i].modifiers()), constraints[i].getTokenReference());
				}
			}
		}
		
		// conjoin universal constraints while translating
		// non-universal (i.e., method-specific) ones separately
		JExpression left = null;
		for (int i = 0; i < constraints.length; i++) {
			// skip uncheckable constraints (e.g., redundant,
			// not requested, or trivially true.
			if (!isCheckable(constraints[i])
					|| (hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
					|| !(privacy(constraints[i].modifiers()) == visibility)){
				continue;
			}

			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				TransPostExpression2 transConstraint = null;
				left = new RacPredicate(constraints[i].predicate());
				if (left != null){
					transConstraint = 
						new TransPostExpression2(mvarGen, null, mvarGen, 
								false, 
								left, null, this.typeDecl, "JMLHistoryConstraintError");

					transConstraint.stmt(true); 

					// list of old expressions
					if(forStatic){
						this.hasOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
						this.oldExprsForStat = transConstraint.oldExprs();
						this.oldExprsDeclForStat = transConstraint.oldVarDecl();
					}
					else{
						this.hasOldExpressions = transConstraint.oldExprs().size() > 0;
						this.oldExprs = transConstraint.oldExprs();
						this.oldExprsDecl = transConstraint.oldVarDecl();	
					}	
				}

				// JML Constraint Error
				errorMsg = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsg += ", " + this.getSpecificConstraintTokenReference(constraints[i], forStatic);
				errorMsg += this.getContextValuesForSpecificConstraint(constraints[i], forStatic, this.varGen);

				// JML Evaluation Error
				evalErrorMsg = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsg += ", " + this.getSpecificConstraintTokenReference(constraints[i], forStatic);
				evalErrorMsg += this.getContextValuesForSpecificConstraint(constraints[i], forStatic, this.varGen);

				String constPred = (forStatic ? transConstraint.stmtAsString() : AspectUtil.changeThisOrSuperRefToAdviceRef(transConstraint.stmtAsString(), typeDecl));
				
				if(Main.aRacOptions.multipleSpecCaseChecking()){
					AspectUtil.getInstance().currentCompilationUnitHasConstraints();
				}
				//generating code
				if(isNotFirst)
					code.append("\n");
				code.append("\n");
				if(forStatic){
					if(visibility == ACC_PUBLIC){
						code.append(this.javadocStat.replace("constraints", "public constraints"));
					}
					else if(visibility == ACC_PROTECTED){
						code.append(this.javadocStat.replace("constraints", "protected constraints"));
					}
					else if(visibility == 0L){
						code.append(this.javadocStat.replace("constraints", "default constraints"));
					}
					else if(visibility == ACC_PRIVATE){
						code.append(this.javadocStat.replace("constraints", "private constraints"));
					}
				}	
				else{
					if(visibility == ACC_PUBLIC){
						code.append(this.javadoc.replace("constraints", "public constraints"));
					}
					else if(visibility == ACC_PROTECTED){
						code.append(this.javadoc.replace("constraints", "protected constraints"));
					}
					else if(visibility == 0L){
						code.append(this.javadoc.replace("constraints", "default constraints"));
					}
					else if(visibility == ACC_PRIVATE){
						code.append(this.javadoc.replace("constraints", "private constraints"));
					}
				}
				code.append("\n");
				this.generateAroundAdviceForSpecificConstraintChecking(
						classQualifiedName, packageQualifiedName, code, errorMsg, evalErrorMsg,
						constPred, this.getMethodNames(constraints[i]
						                                           .methodNames().methodNameList()), forStatic, visibility);
				isNotFirst = true;
			}
		}

		return code.toString();
	}

	private String[] getMethodNames(JmlMethodName[] names) {
		String [] methodNames = new String[names.length];
		for (int i = 0; i < names.length; i++) {
			methodNames[i] = AspectUtil.removeThisSuperOrConstructorRefToAdvicePC(names[i].toString(), typeDecl);
		}    
		return methodNames;
	}

	protected /*@ pure @*/ boolean canInherit() {
		// TODO Auto-generated method stub
		return false;
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------
	/** The variable generator to be used in the translation. If
	 * necessary, fresh variables are generated by this translator
	 * using this variable generator during the translation.
	 */
	private final /*@ spec_public non_null @*/ VarGenerator varGen;

	private /*@ nullable */ String javadocStat;

	private String publicInstConstPred = "";
	private String protectedInstConstPred = "";
	private String defaultInstConstPred = "";
	private String privateInstConstPred = "";
	private String publicStatConstPred = "";
	private String protectedStatConstPred = "";
	private String defaultStatConstPred = "";
	private String privateStatConstPred = "";
	
	private boolean hasInstConst;
	private boolean hasStatConst;
	private boolean hasPublicInstConst = false;
	private boolean hasProtectedInstConst = false;
	private boolean hasDefaultInstConst = false;
	private boolean hasPrivateInstConst = false;
	private boolean hasPublicStatConst = false;
	private boolean hasProtectedStatConst = false;
	private boolean hasDefaultStatConst = false;
	private boolean hasPrivateStatConst = false;

	private boolean hasOldExpressions;
	private boolean hasOldExpressionsForStat;
	private boolean hasPublicOldExpressions;
	private boolean hasPublicOldExpressionsForStat;
	private boolean hasProtectedOldExpressions;
	private boolean hasProtectedOldExpressionsForStat;
	private boolean hasDefaultOldExpressions;
	private boolean hasDefaultOldExpressionsForStat;
	private boolean hasPrivateOldExpressions;
	private boolean hasPrivateOldExpressionsForStat;
	
	private List oldExprs;
	private List oldExprsDecl;
	private List oldExprsForStat;
	private List oldExprsDeclForStat;
	
	
	private List publicOldExprs;
	private List publicOldExprsDecl;
	private List publicOldExprsForStat;
	private List publicOldExprsDeclForStat;
	private List protectedOldExprs;
	private List protectedOldExprsDecl;
	private List protectedOldExprsForStat;
	private List protectedOldExprsDeclForStat;
	private List defaultOldExprs;
	private List defaultOldExprsDecl;
	private List defaultOldExprsForStat;
	private List defaultOldExprsDeclForStat;	
	private List privateOldExprs;
	private List privateOldExprsDecl;
	private List privateOldExprsForStat;
	private List privateOldExprsDeclForStat;
}

