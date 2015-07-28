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
 * $Id: AspectUtil.java,v 1.0 2009/03/27 16:48:06 henriquerebelo Exp $
 */

package org.jmlspecs.util;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;

import org.jmlspecs.ajmlrac.RacConstants;
import org.jmlspecs.ajmlrac.TransUtils;
import org.jmlspecs.checker.JmlAbstractVisitor;
import org.jmlspecs.checker.JmlBehaviorSpec;
import org.jmlspecs.checker.JmlExceptionalBehaviorSpec;
import org.jmlspecs.checker.JmlFormalParameter;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlNormalBehaviorSpec;
import org.jmlspecs.checker.JmlSpecCase;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JMethodDeclarationType;

import com.thoughtworks.qdox.JavaDocBuilder;
import com.thoughtworks.qdox.model.Annotation;
import com.thoughtworks.qdox.model.JavaClass;
import com.thoughtworks.qdox.model.JavaMethod;
import com.thoughtworks.qdox.model.JavaParameter;

public class AspectUtil {

	private static AspectUtil instance = null;

	private StringBuffer preconditionPointcuts = null;
	private List interfaceStaticModelFields = null;
	private List defaultSignalsClauseTokenRefereces = null;
	private List defaultEnsuresClauseTokenRefereces = null;
	private List defaultRequiresClauseTokenRefereces = null;
	private List preconditionNewMethodsAdvice = null;
	private List postconditionNewMethodsAfterAdvice = null;
	private List postconditionNewMethodsAroundAdvice = null;
	private List preconditionNewMethodsAdviceXCS = null;
	private List postconditionNewMethodsAfterAdviceXCS = null;
	private List postconditionNewMethodsAroundAdviceXCS = null;
	private List crossrefs = null;
	private List quantifierInnerClasses = null;
	private List quantifierUniqueID = null;
	private List crosscutSpecMeths = null;
	private List aspectAdvice = null;
	private List aspectDecl = null;
	private List exceptionsInSignalsClausesInCompilationUnit = null;
	private boolean aroundAdvice = false;
	private int uniqueVarGenForQuantifier = 0;
	private boolean currentCompilationUnitInvariants = false;
	private boolean currentCompilationUnitConstraints = false;
	public boolean isCompilationUnitRacable = false;

	// for multiple spec case checking
	public HashMap preconditionSpecCases = null;
	public HashMap nPostconditionSpecCases = null;
	public HashMap publicPreconditionSpecCases = null;
	public HashMap protectedPreconditionSpecCases = null;
	public HashMap defaultPreconditionSpecCases = null;
	public HashMap privatePreconditionSpecCases = null;
	public HashMap publicNPostconditionSpecCases = null;
	public HashMap protectedNPostconditionSpecCases = null;
	public HashMap defaultNPostconditionSpecCases = null;
	public HashMap privateNPostconditionSpecCases = null;

	public HashMap nPostconditionForContextSpecCases = null;
	public HashMap xPostconditionForContextSpecCases = null;
	public HashMap publicNPostconditionForContextSpecCases = null;
	public HashMap publicXPostconditionForContextSpecCases = null;
	public HashMap protectedNPostconditionForContextSpecCases = null;
	public HashMap protectedXPostconditionForContextSpecCases = null;
	public HashMap defaultNPostconditionForContextSpecCases = null;
	public HashMap defaultXPostconditionForContextSpecCases = null;
	public HashMap privateNPostconditionForContextSpecCases = null;
	public HashMap privateXPostconditionForContextSpecCases = null;

	public HashMap nPostTokenReferenceSpecCases = null;
	public HashMap xPostTokenReferenceSpecCases = null;
	public HashMap publicNPostTokenReferenceSpecCases = null;
	public HashMap publicXPostTokenReferenceSpecCases = null;
	public HashMap protectedNPostTokenReferenceSpecCases = null;
	public HashMap protectedXPostTokenReferenceSpecCases = null;
	public HashMap defaultNPostTokenReferenceSpecCases = null;
	public HashMap defaultXPostTokenReferenceSpecCases = null;
	public HashMap privateNPostTokenReferenceSpecCases = null;
	public HashMap privateXPostTokenReferenceSpecCases = null;

	// for crosscutting contract specification
	private JavaDocBuilder qDoxFile = null;
	public boolean hasThisRef = false;
	public boolean isStaticPC = false;

	public void initializeMethodSpecCaseCheckingContent(){
		this.preconditionSpecCases = new HashMap();
		this.nPostconditionSpecCases = new HashMap();
		this.publicPreconditionSpecCases = new HashMap();
		this.protectedPreconditionSpecCases = new HashMap();
		this.defaultPreconditionSpecCases = new HashMap();
		this.privatePreconditionSpecCases = new HashMap();
		this.publicNPostconditionSpecCases = new HashMap();
		this.protectedNPostconditionSpecCases = new HashMap();
		this.defaultNPostconditionSpecCases = new HashMap();
		this.privateNPostconditionSpecCases = new HashMap();
		this.nPostconditionForContextSpecCases = new HashMap();
		this.xPostconditionForContextSpecCases = new HashMap();
		this.publicNPostconditionForContextSpecCases = new HashMap();
		this.publicXPostconditionForContextSpecCases = new HashMap();
		this.protectedNPostconditionForContextSpecCases = new HashMap();
		this.protectedXPostconditionForContextSpecCases = new HashMap();
		this.defaultNPostconditionForContextSpecCases = new HashMap();
		this.defaultXPostconditionForContextSpecCases = new HashMap();
		this.privateNPostconditionForContextSpecCases = new HashMap();
		this.privateXPostconditionForContextSpecCases = new HashMap();
		this.nPostTokenReferenceSpecCases = new HashMap();
		this.xPostTokenReferenceSpecCases = new HashMap();
		this.publicNPostTokenReferenceSpecCases = new HashMap();
		this.publicXPostTokenReferenceSpecCases = new HashMap();
		this.protectedNPostTokenReferenceSpecCases = new HashMap();
		this.protectedXPostTokenReferenceSpecCases = new HashMap();
		this.defaultNPostTokenReferenceSpecCases = new HashMap();
		this.defaultXPostTokenReferenceSpecCases = new HashMap();
		this.privateNPostTokenReferenceSpecCases = new HashMap();
		this.privateXPostTokenReferenceSpecCases = new HashMap();
	}

	private AspectUtil(){
		this.interfaceStaticModelFields = new ArrayList();
		this.preconditionPointcuts = new StringBuffer();
		this.defaultSignalsClauseTokenRefereces = new ArrayList();
		this.defaultEnsuresClauseTokenRefereces = new ArrayList();
		this.defaultRequiresClauseTokenRefereces = new ArrayList();
		this.preconditionNewMethodsAdvice = new ArrayList();
		this.postconditionNewMethodsAfterAdvice = new ArrayList();
		this.postconditionNewMethodsAroundAdvice = new ArrayList();
		this.preconditionNewMethodsAdviceXCS = new ArrayList();
		this.postconditionNewMethodsAfterAdviceXCS = new ArrayList();
		this.postconditionNewMethodsAroundAdviceXCS = new ArrayList();
		this.crossrefs = new ArrayList();
		this.quantifierInnerClasses = new ArrayList();
		this.quantifierUniqueID = new ArrayList();
		this.crosscutSpecMeths = new ArrayList();
		this.aspectAdvice = new ArrayList();
		this.aspectDecl = new ArrayList();
		this.qDoxFile = new JavaDocBuilder();
		this.exceptionsInSignalsClausesInCompilationUnit = new ArrayList();
	}

	public static AspectUtil getInstance(){
		if(instance == null){
			instance = new AspectUtil();
		}
		return instance;
	}

	public void emptyInterfaceStaticModelFields() {
		this.interfaceStaticModelFields.clear();
	}

	public void emptyPreconditionNewMethodsAdvice() {
		this.preconditionNewMethodsAdvice.clear();
	}

	public void emptyPostconditionNewMethodsAfterAdvice() {
		this.postconditionNewMethodsAfterAdvice.clear();
	}

	public void emptyPostconditionNewMethodsAroundAdvice() {
		this.postconditionNewMethodsAroundAdvice.clear();
	}
	
	public void emptyPreconditionNewMethodsAdviceXCS() {
		this.preconditionNewMethodsAdviceXCS.clear();
	}

	public void emptyPostconditionNewMethodsAfterAdviceXCS() {
		this.postconditionNewMethodsAfterAdviceXCS.clear();
	}

	public void emptyPostconditionNewMethodsAroundAdviceXCS() {
		this.postconditionNewMethodsAroundAdviceXCS.clear();
	}
	
	public void emptyCrossrefs() {
		this.crossrefs.clear();
	}

	public void emptyQuantifierInnerClasses() {
		this.quantifierInnerClasses.clear();
	}

	public void emptyQuantifierUniqueID(){
		this.quantifierUniqueID.clear();
	}
	
	public void emptyExceptionsInSignalsClausesInCompilationUnit() {
		this.exceptionsInSignalsClausesInCompilationUnit.clear();
	}

	public boolean isAroundAdvice(){
		return this.aroundAdvice;
	}

	public int getUniqueVarGenForQuantifier(){
		return this.uniqueVarGenForQuantifier++;
	}

	public boolean hasPreconditionPointcuts(){
		return this.preconditionPointcuts.length() > 0;
	}

	public void setAroundAdvice(boolean b){
		this.aroundAdvice = b;
	}

	public List getInterfaceStaticModelFields() {
		return this.interfaceStaticModelFields;
	}

	public List getPreconditionNewMethodsAdvice() {
		return this.preconditionNewMethodsAdvice;
	}

	public List getPostconditionNewMethodsAfterAdvice() {
		return this.postconditionNewMethodsAfterAdvice;
	}

	public List getPostconditionNewMethodsAroundAdvice() {
		return this.postconditionNewMethodsAroundAdvice;
	}
	
	public List getPreconditionNewMethodsAdviceXCS() {
		return this.preconditionNewMethodsAdviceXCS;
	}

	public List getPostconditionNewMethodsAfterAdviceXCS() {
		return this.postconditionNewMethodsAfterAdviceXCS;
	}

	public List getPostconditionNewMethodsAroundAdviceXCS() {
		return this.postconditionNewMethodsAroundAdviceXCS;
	}

	public List getCrossrefs() {
		return this.crossrefs;
	}

	public List getQuantifierUniqueIDs(){
		return this.quantifierUniqueID;
	}

	public List getQuantifierInnerClasses(){
		return this.quantifierInnerClasses;
	}
	
	public List getExceptionsInSignalsClausesInCompilationUnit(){
		return this.exceptionsInSignalsClausesInCompilationUnit;
	}

	public String getQuantifierInnerClassByID(String quantifierID){
		String result = "";
		for (Iterator iterator = quantifierInnerClasses.iterator(); iterator.hasNext();) {
			String currentQtf = (String) iterator.next();
			if(currentQtf.contains(quantifierID)){
				result = currentQtf;
				break;
			}
		}
		return result;
	}

	public String getQuantifierInnerClassesForTrans(String pred){
		StringBuffer result = new StringBuffer();
		result.append("");
		if(pred.contains(RacConstants.CN_RAC_QUANTIFIER_ID)){
			List ids = AspectUtil.getInstance().getQuantifierUniqueIDs();
			for (Iterator iterator = ids.iterator(); iterator.hasNext();) {
				String currentID = (String) iterator.next();
				if(pred.contains(currentID)){
					String qcode = AspectUtil.getInstance().getQuantifierInnerClassByID(currentID);
					result.append(qcode+"\n");

				}
			}
		}
		return result.toString();
	}

	public void appendInterfaceStaticModelFields(String modelField) {
		this.interfaceStaticModelFields.add(modelField);
	}

	public void appendPreconditionNewMethodsAdvice(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.preconditionNewMethodsAdvice.add(meth);
	}

	public void appendPostconditionNewMethodsAfterAdvice(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.postconditionNewMethodsAfterAdvice.add(meth);
	}

	public void appendPostconditionNewMethodsAroundAdvice(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.postconditionNewMethodsAroundAdvice.add(meth);
	}
	
	public void appendPreconditionNewMethodsAdviceXCS(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.preconditionNewMethodsAdviceXCS.add(meth);
	}

	public void appendPostconditionNewMethodsAfterAdviceXCS(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.postconditionNewMethodsAfterAdviceXCS.add(meth);
	}

	public void appendPostconditionNewMethodsAroundAdviceXCS(JMethodDeclarationType meth){
		this.isCompilationUnitRacable = true;
		this.postconditionNewMethodsAroundAdviceXCS.add(meth);
	}
	
	public void appendCrossrefPointcut(String crossrefPC){
		this.crossrefs.add(crossrefPC);
	}

	public void appendQuantifierInnerClasses(String quantifierInnerClass){
		this.quantifierInnerClasses.add(quantifierInnerClass);
	}

	public void appendQuantifierUniqueID(String quantifierID){
		this.quantifierUniqueID.add(quantifierID);
	}

	public void appendCrosscutSpecMeth(JavaMethod crosscutSpecMeth){
		this.crosscutSpecMeths.add(crosscutSpecMeth);
	}

	public void appendAspectAdvice(JavaMethod adviceOrPC){
		this.aspectAdvice.add(adviceOrPC);
	}

	public void appendAspectDecl(JavaClass aspect){
		this.aspectDecl.add(aspect);
	}
	
	public void appendExceptionInSignalsClauseInCompilationUnit(CType exception){
		if(!exception.toString().startsWith("java.lang")){
			boolean can = true;
			for (Iterator<CType> iterator = 
					this.exceptionsInSignalsClausesInCompilationUnit.iterator(); iterator
					.hasNext();) {
				CType cType = iterator.next();
				if(cType.toString().equals(exception.toString())){
					can = false;
					break;
				}
			}
			if(can){
				this.exceptionsInSignalsClausesInCompilationUnit.add(exception);
			}
		}
	}

	public void emptyPreconditionPointcuts(){
		this.preconditionPointcuts = new StringBuffer();
	}

	public void appendPreconditionPointcut(String pc){
		if(this.preconditionPointcuts.length() == 0)
			this.preconditionPointcuts.append(pc);
		else
			this.preconditionPointcuts.append("\n").
			append("         ").append(" || ").append(pc);
	}

	public String getPreconditionPointcut(){
		String pc = this.preconditionPointcuts.toString();
//		pc = pc.replaceAll("&&(\\s)*this\\((\\s)*object\\$rac(\\s)*\\)", "").
//				replaceAll("&&(\\s)*target\\((\\s)*object\\$rac(\\s)*\\)", "").
//				replaceAll("&&(\\s)*args\\([^\\)]+\\)", "");
		return AspectUtil.processMethSig("("+pc+")");
	}

	public void currentCompilationUnitHasInvariants(){
		this.isCompilationUnitRacable = true;
		this.currentCompilationUnitInvariants = true;
	}

	public void resetCurrentCompilationUnitHasInvariants(){
		this.currentCompilationUnitInvariants = false;
	}

	public void currentCompilationUnitHasConstraints(){
		this.isCompilationUnitRacable = true;
		this.currentCompilationUnitConstraints = true;
	}

	public void resetCurrentCompilationUnitHasConstraints(){
		this.currentCompilationUnitConstraints = false;
	}

	public boolean hasInvariantsInCurrentCompilationUnit(){
		return this.currentCompilationUnitInvariants;
	}

	public boolean hasConstraintsInCurrentCompilationUnit(){
		return this.currentCompilationUnitConstraints;
	}

	public void appendDefaultSignalsClauseTokenRefereces(String tokenReference){
		this.defaultSignalsClauseTokenRefereces.add(tokenReference);
	}

	public List getDefaultSignalsClauseTokenRefereces(){
		return this.defaultSignalsClauseTokenRefereces;
	}

	public void appendDefaultEnsuresClauseTokenRefereces(String tokenReference){
		this.defaultEnsuresClauseTokenRefereces.add(tokenReference);
	}

	public List getDefaultEnsuresClauseTokenRefereces(){
		return this.defaultEnsuresClauseTokenRefereces;
	}

	public void appendDefaultRequiresClauseTokenRefereces(String tokenReference){
		this.defaultRequiresClauseTokenRefereces.add(tokenReference);
	}

	public List getDefaultRequiresClauseTokenRefereces(){
		return this.defaultRequiresClauseTokenRefereces;
	}

	public List getCrosscutSpecMeths(){
		return this.crosscutSpecMeths;
	}

	public List getAspectAdviceOrPCs(){
		return this.aspectAdvice;
	}

	public List getAspectDecls(){
		return this.aspectDecl;
	}

	public static String changeThisOrSuperRefToAdviceRef(String pred, JmlTypeDeclaration typeDecl){
		// handling common replacements
		pred = pred.replace("this.", "object$rac.");
		try {
			pred = pred.replace(typeDecl.getCClass().getJavaName()+".object$rac.", "object$rac.");
			pred = pred.replace(typeDecl.getCClass().ident()+".object$rac.", "object$rac.");
			pred = pred.replace("super.", "(("+typeDecl.getCClass().getSuperClass().getJavaName()+")object$rac).");
			for (Iterator iterator = typeDecl.inners().iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				pred = pred.replace("super.", "(("+currentInnerType.getCClass().getSuperClass().getJavaName()+")object$rac).");
			}
			pred = pred.replace("delegee_"+typeDecl.ident()+"().", "");
			pred = pred.replaceAll("\\bthis\\b", Matcher.quoteReplacement("object$rac"));
		} catch (Exception e) {}
		return pred;
	}

	public static String removeThisSuperOrConstructorRefToAdvicePC(String methodName, JmlTypeDeclaration typeDecl){
		methodName = methodName.replace("this.", "");
		methodName = methodName.replace("super.", "");
		int index = methodName.indexOf(typeDecl.ident());
		if(!(index == -1))
			methodName = methodName.substring(index).replace(typeDecl.ident(), "new");
		return methodName;
	}

	public static String replaceDollaSymbol(String member){
		return member.replace("$", ".");
	}

	public static String processMethSig(String sig){
		return sig.replace("\\bigint", "java.math.BigInteger");
	}

	public static boolean hasAssertion(String pred){
		if(pred == null){
			return false;
		}
		boolean result = ((!pred.equals("")) && (!pred.equals(" ")) && (!pred.equals("true")) 
				&& (!pred.equals("(true)")) && (!pred.equals("null")));
//		boolean result = ((!pred.equals("")) && (!pred.equals(" ")) && (!pred.equals("null")));
		return result;
	}
	
	public static boolean hasPrecondition(String pred){
		if(pred == null){
			return false;
		}
//		boolean result = ((!pred.equals("")) && (!pred.equals(" ")) && (!pred.equals("true")) 
//				&& (!pred.equals("(true)")) && (!pred.equals("null")));
		boolean result = ((!pred.equals("")) && (!pred.equals(" ")) && (!pred.equals("null")));
		return result;
	}

	public void addJavaFileAsString(String file){
		qDoxFile.addSource(new StringReader(file));
	}

	public List<JavaMethod> getAllDeclaredJavaMethodsInFile(String typeFullQualifiedName){
		List<JavaMethod> result = new ArrayList<JavaMethod>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			if(currentJavaDeclType.getFullyQualifiedName().equals(typeFullQualifiedName)){
				JavaMethod [] javaDeclMethods = currentJavaDeclType.getMethods();
				for (int j = 0; j < javaDeclMethods.length; j++) {
					JavaMethod currentJavaDeclMethod = javaDeclMethods[j];
					result.add(currentJavaDeclMethod);
				}
			}
		}
		Comparator<JavaMethod> COMPARE_BY_LINE_NUMBER = new Comparator<JavaMethod>() {
			public int compare(JavaMethod one, JavaMethod other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	public JavaMethod getCorrespondingJavaMethodThroughJMLMethod(String typeFullQualifiedName, JmlMethodDeclaration methodDecl){
		JavaMethod javaMethod = null;
		List<JavaMethod> javaMeths = AspectUtil.getInstance().getAllDeclaredJavaMethodsInFile(typeFullQualifiedName);
		String jmlMeth = methodDecl.ident()+AspectUtil.generateMethodParameters(methodDecl.parameters(), false);
		boolean needsImportCompletion = AspectUtil.needsImportCompletion(methodDecl.parameters());
		for (Iterator<JavaMethod> iterator = javaMeths.iterator(); iterator.hasNext();) {
			JavaMethod currentJavaMeth = iterator.next();
			String currentMethSig = currentJavaMeth.getName()+AspectUtil.generateMethodParameters(currentJavaMeth.getParameters(), false);
			if(jmlMeth.equals(currentMethSig)){
				javaMethod = currentJavaMeth;
				break;
			}
			else if(needsImportCompletion){
				String methodNameWithParameterTypesCompletion = methodDecl.ident()+AspectUtil.generatePossibleMethodParametersMatch(methodDecl.parameters(), currentJavaMeth.getParameters()).toString();
				if(methodNameWithParameterTypesCompletion.equals(currentMethSig)){
					javaMethod = currentJavaMeth;
					break;
				}
			}
		}
		
		return javaMethod;
	}

	public static StringBuffer generateMethodParametersForAdvicePointcut(JFormalParameter[] parameters) {
		final StringBuffer code = new StringBuffer("");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0)
					code.append(", ");
				parameters[i].accept( new JmlAbstractVisitor() {
					public void	visitJmlFormalParameter(
							JmlFormalParameter self) {
						CType actualType = self.getType();
						code.append(actualType.toString());
					}
				});
			}
		}
		return code;
	}

	public static String generateMethodParameters(CSpecializedType[] parameters) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0) {
					code.append(", ");	
				}
				CType actualType = parameters[i].staticType();
				code.append(TransUtils.toString(actualType));
			}
		}
		code.append(")");
		return code.toString();
	}

	public static StringBuffer generateMethodParameters(JFormalParameter[] parameters, final boolean includeIdentName) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0) {
					code.append(", ");	
				}
				parameters[i].accept( new JmlAbstractVisitor() {
					public void	visitJmlFormalParameter(
							JmlFormalParameter self) {
						CType actualType = self.getType();
						String ident = self.ident();
						code.append(TransUtils.toString(actualType));
						if(includeIdentName){
							code.append(" ");
							code.append(ident);
						}
					}
				});	
			}
		}
		code.append(")");
		return code;
	}
	
	public static StringBuffer generateMethodParametersOnlyParamNames(JFormalParameter[] parameters) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0) {
					code.append(", ");	
				}
				parameters[i].accept( new JmlAbstractVisitor() {
					public void	visitJmlFormalParameter(
							JmlFormalParameter self) {
						CType actualType = self.getType();
						String ident = self.ident();
						code.append(ident);
					}
				});	
			}
		}
		code.append(")");
		return code;
	}

	public static StringBuffer generateMethodParameters(JavaParameter[] parameters, boolean includeIdentName) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0){
					code.append(", ");	
				}
				code.append(parameters[i].getType()+"".replace("$", "."));
				if(includeIdentName){
					code.append(" ");
					code.append(parameters[i].getName());
				}
			}
		}
		code.append(")");
		return code;
	}
	
	public static StringBuffer generateMethodParametersOnlyParamNames(JavaParameter[] parameters) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0){
					code.append(", ");	
				}
				code.append(parameters[i].getName());
			}
		}
		code.append(")");
		return code;
	}
	
	public static boolean needsImportCompletion(JFormalParameter[] parameters) {
		boolean result = false;
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				CType actualType = parameters[i].getType();
				String type = TransUtils.toString(actualType);
				if(!type.contains(".")){
					result = true;
				}
			}
		}
		
		return result;
	}
	
	public static boolean needsImportCompletionArgumentType(String parameter) {
		boolean result = false;
		if(!parameter.contains(".")){
			result = true;
		}
		
		return result;
	}
	
	public static StringBuffer generatePossibleMethodParametersMatch(JFormalParameter[] parameters, JavaParameter[] parametersCompletion) {
		final StringBuffer code = new StringBuffer("");
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0) {
					code.append(", ");	
				}
				CType actualType = parameters[i].getType();
				if(AspectUtil.needsImportCompletionArgumentType(TransUtils.toString(actualType)) && (parameters.length == parametersCompletion.length)){
					String parameterCompletion = parametersCompletion[i].getType()+"".replace("$", ".");
					if(parameterCompletion.endsWith(TransUtils.toString(actualType))){
						code.append(parameterCompletion);
					}
					else{
						code.append(TransUtils.toString(actualType));
					}
				}
				else{
					code.append(TransUtils.toString(actualType));
				}
				
			}
		}
		code.append(")");
		return code;
	}
	
//	public List getCompilationUnitImports() {
//		List imports = new ArrayList();
//		String [] importsqDox = qDoxFile.getSources()[0].getImports();
//		for (int i = 0; i < importsqDox.length; i++) {
//			String importt = importsqDox[i].substring(0, (importsqDox[i].lastIndexOf(".")+1));
//			if(!imports.contains(importt)){
//				imports.add(importt);
//			}
//		}
//		
//		return imports;
//	}
	
	private boolean isParameterEquivalent(JFormalParameter[] parameters, JavaParameter[] parameters2){
		boolean result = true;
		
		if(parameters.length == parameters2.length){
			for (int i = 0; i < parameters.length; i++) {
				CType actualType = parameters[i].getType();
				String paramType = TransUtils.toString(actualType);
				String paramType2 = parameters2[i].getType()+"".replace("$", ".");
				if(!(paramType.equals(paramType2))){
					if(paramType.lastIndexOf(".") != -1){
						paramType = paramType.substring((paramType.lastIndexOf(".")+1), (paramType.length()));
						if(!(paramType.equals(paramType2))){
							result = false;
							break;
						}
					}
					else {
						result = false;
						break;
					}
				}
			}
		}
		else {
			result = false;
		}
		
		return result;
	}

	public boolean isCrosscutSpecChecking(JmlMethodDeclaration methodDecl){
		boolean isCrosscutSpecMeth = false;
		String classQualifiedName = methodDecl.getMethod().owner().getJavaName();
		String methodNameWithParameterTypes = methodDecl.ident()+AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
		boolean needsImportCompletion = AspectUtil.needsImportCompletion(methodDecl.parameters());
		List javaMethCrosscutSpecChecking = this.getCrosscutSpecMeths();
		for (Iterator iterator = javaMethCrosscutSpecChecking.iterator(); iterator
				.hasNext();) {
			JavaMethod currentJavaMethod = (JavaMethod) iterator.next();
			if(classQualifiedName.equals(currentJavaMethod.getParentClass().getFullyQualifiedName())){
				String currentJavaMethNameWithParameterTypes = currentJavaMethod.getName()+
						AspectUtil.generateMethodParameters(currentJavaMethod.getParameters(), false).toString();
				if(methodNameWithParameterTypes.equals(currentJavaMethNameWithParameterTypes)){
					isCrosscutSpecMeth = true;
					break;
				}
				else if(methodDecl.ident().equals(currentJavaMethod.getName())){
					if(isParameterEquivalent(methodDecl.parameters(), currentJavaMethod.getParameters())){
						isCrosscutSpecMeth = true;
						break;
					}
				}
				else if(needsImportCompletion){
					String methodNameWithParameterTypesCompletion = methodDecl.ident()+AspectUtil.generatePossibleMethodParametersMatch(methodDecl.parameters(), currentJavaMethod.getParameters()).toString();
					if(methodNameWithParameterTypesCompletion.equals(currentJavaMethNameWithParameterTypes)){
						isCrosscutSpecMeth = true;
						break;
					}
				}
			}
		}
		// check if besides pc declaration it really has JML specs
		if(isCrosscutSpecMeth){
			// if does not have JML specs, it is only considered an ordinary pointcut declaration for AspectJ... [[[hemr]]]
			if(!(methodDecl.hasSpecification() && methodDecl.methodSpecification().hasSpecCases())){
				isCrosscutSpecMeth = false;
			}
		}
		return isCrosscutSpecMeth;
	}
	
	public boolean isXCSFlexible(JavaMethod jm){
		boolean result = false;
		for (int i = 0; i < jm.getAnnotations().length; i++) {
    		Annotation currentAnno = jm.getAnnotations()[i];
    		if((currentAnno.toString().startsWith("@org.jmlspecs.lang.annotation.FlexibleXCS")) || 
    				(currentAnno.toString().startsWith("@org.jmlspecs.lang.annotation.GlobalXCS"))){
    			result = true;
    		}
    	}
		return result;
	}
	
	public boolean isHashCodeMeth(JmlMethodDeclaration methodDecl){
		boolean isHashCodeMeth = false;
		
		if(methodDecl.ident().equals("hashCode")){
			if((methodDecl.returnType().toString().equals("int")) && (methodDecl.parameters().length == 0)){
				isHashCodeMeth = true;
			}
		}
		return isHashCodeMeth;
	}

	public JavaMethod getJavaMethCrosscutSpecChecking(JmlMethodDeclaration methodDecl){
		JavaMethod result = null;
		String classQualifiedName = methodDecl.getMethod().owner().getJavaName();
		String methodNameWithParameterTypes = methodDecl.ident()+AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
		boolean needsImportCompletion = AspectUtil.needsImportCompletion(methodDecl.parameters());
		List javaMethXCS = this.getCrosscutSpecMeths();
		for (Iterator iterator = javaMethXCS.iterator(); iterator
				.hasNext();) {
			JavaMethod currentJavaMethod = (JavaMethod) iterator.next();
			if(classQualifiedName.equals(currentJavaMethod.getParentClass().getFullyQualifiedName())){
				String currentJavaMethNameWithParameterTypes = currentJavaMethod.getName()+AspectUtil.generateMethodParameters(currentJavaMethod.getParameters(), false).toString();
				if(methodNameWithParameterTypes.equals(currentJavaMethNameWithParameterTypes)){
					result = currentJavaMethod;
					break;
				}
				else if(methodDecl.ident().equals(currentJavaMethod.getName())){
					if(isParameterEquivalent(methodDecl.parameters(), currentJavaMethod.getParameters())){
						result = currentJavaMethod;
						break;
					}
				}
				else if(needsImportCompletion){
					String methodNameWithParameterTypesCompletion = methodDecl.ident()+AspectUtil.generatePossibleMethodParametersMatch(methodDecl.parameters(), currentJavaMethod.getParameters()).toString();
					if(methodNameWithParameterTypesCompletion.equals(currentJavaMethNameWithParameterTypes)){
						result = currentJavaMethod;
						break;
					}
				}
			}
		}
		return result;
	}

	public boolean isCrosscuttingContractSpecificationDeclAsAspect(JavaMethod methodDecl){
		boolean isCrosscutSpec = false;
		for (int i = 0; i < methodDecl.getParentClass().getAnnotations().length; i++) {
			if(methodDecl.getParentClass().getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Aspect")){
				isCrosscutSpec = true;
			}
		}
		return isCrosscutSpec;
	}
	
	public boolean isCrosscuttingContractSpecificationForInterface(JavaMethod methodDecl){
		boolean isCrosscutSpecForInterface = false;
		if(methodDecl.getParentClass().getParentClass() != null){
			if(methodDecl.getParentClass().getParentClass().isInterface()){
				for (int i = 0; i < methodDecl.getParentClass().getAnnotations().length; i++) {
					if(methodDecl.getParentClass().getAnnotations()[i].toString().startsWith("@org.jmlspecs.lang.annotation.InterfaceXCS()")){
						isCrosscutSpecForInterface = true;
					}
				}
			}
		}
		return isCrosscutSpecForInterface;
	}

	public boolean isAspectAdvice(JmlMethodDeclaration methodDecl){
		boolean isAspectMeth = false;
		String classQualifiedName = methodDecl.getMethod().owner().getJavaName();
		String methodNameWithParameterTypes = methodDecl.ident()+AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
		List javaAspectMeth = this.getAspectAdviceOrPCs();
		for (Iterator iterator = javaAspectMeth.iterator(); iterator
				.hasNext();) {
			JavaMethod currentJavaMethod = (JavaMethod) iterator.next();
			if(classQualifiedName.equals(currentJavaMethod.getParentClass().getFullyQualifiedName())){
				String currentJavaMethNameWithParameterTypes = currentJavaMethod.getName()+
						AspectUtil.generateMethodParameters(currentJavaMethod.getParameters(), false).toString();
				if(methodNameWithParameterTypes.equals(currentJavaMethNameWithParameterTypes)){
					isAspectMeth = true;
					break;
				}
				else if(methodDecl.ident().equals(currentJavaMethod.getName())){
					if(isParameterEquivalent(methodDecl.parameters(), currentJavaMethod.getParameters())){
						isAspectMeth = true;
						break;
					}
				}
			}
		}
		return isAspectMeth;
	}

	public boolean isTypeDeclAnAspect(JmlTypeDeclaration typeDecl){
		boolean isAspectDecl = false;
		String classQualifiedName = AspectUtil.replaceDollaSymbol(typeDecl.getCClass().getJavaName());
		List aspectDecls = this.getAspectDecls();
		for (Iterator iterator = aspectDecls.iterator(); iterator.hasNext();) {
			JavaClass currentAspect = (JavaClass) iterator.next();
			if(AspectUtil.replaceDollaSymbol(currentAspect.getFullyQualifiedName()).equals(classQualifiedName)){
				isAspectDecl = true;
				break;
			}
		}
		return isAspectDecl;
	}
	
	public boolean isOldVarReferencedWithinPrecondition(HashMap preconditions, String oldVarIdent){
		boolean result = false;
		
		for (Iterator iterator = preconditions.keySet().iterator(); iterator.hasNext();) {
			int index = (int) iterator.next();
			String precondition = (String)preconditions.get(index);
			if(precondition.contains(oldVarIdent)){
				result = true;
				break;
			}
		}
		
		return result;
	}
	
	public boolean isOldVarReferencedWithinPreExpr(List prexpList, String oldVarIdent){
		boolean result = false;
		
		for (Iterator iterator = prexpList.iterator(); iterator.hasNext();) {
			String prexp = (String)iterator.next();
			if(prexp.contains(oldVarIdent)){
				result = true;
				break;
			}
		}
		
		return result;
	}
	
	public boolean hasElementsStoredOldExpressions(HashMap oldExprs){
		boolean result = false;
		for (Iterator iterator = oldExprs.keySet().iterator(); iterator.hasNext();) {
			int index = (int) iterator.next();
			List currentOldList = (List) oldExprs.get(index);
			if(currentOldList != null){
				if(currentOldList.size() > 0){
					result = true;
					break;
				}
			}
			
		}
		return result;
	}
	
	public boolean hasBehavioralSpec(JmlMethodDeclaration methodDecl){
		boolean hasBehavioralKindSpec = false;
		if(methodDecl.methodSpecification().hasSpecCases()){
			JmlSpecCase[] specCases = methodDecl.methodSpecification().specCases();
			for (int i = 0; i < specCases.length; i++) {
				if(specCases[i] instanceof JmlBehaviorSpec){
					hasBehavioralKindSpec = true;
				}
				else if(specCases[i] instanceof JmlNormalBehaviorSpec){
					hasBehavioralKindSpec = true;
				}
				else if(specCases[i] instanceof JmlExceptionalBehaviorSpec){
					hasBehavioralKindSpec = true;
				}
			}
		}
		return hasBehavioralKindSpec;
	}
}
