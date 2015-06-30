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
 * $Id: InvariantMethodAdviceAsPreconditionMethodClientAwareChecking.java,v 1.0 2013/08/1 11:29:00 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.JMethodDeclarationType;

/**
 * A class for generating assertion check methods for class-level
 * assertions such as invariants and history constraints.
 * There are two types of class-level assertions:
 * <em>instance</em> (<em>non-static</em>) <em>assertions</em> and
 * <em>class</em> (<em>static</em>) <em>assertions</em>.
 * As thus, two types of assertion check methods are generated. 
 * An instance assertion check method checks both the instance and class 
 * assertions while a class assertion check method checks only the class 
 * assertionss. 
 * The generated assertion check methods inherit assertions of its superclass
 * interfaces by dynamically invoking the corresponding assertion methods.
 *
 * <p>
 * The class implements a variant of the <em>Template Pattern</em>
 * [GoF95], prescribed in the class {@link AssertionMethod}.
 * </p>
 *
 * @see AssertionMethod
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public class InvariantMethodAdviceAsPreconditionMethodClientAwareChecking extends InvariantLikeMethodClientAwareChecking{
	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/** Construct a new <code>InvariantLikeMethod</code> object. 
	 *
	 * @param isStatic the kind of assertion check method to generate;
	 *                 <tt>true</tt> for static and <tt>false</tt> for 
	 *                 non-static (instance) assertion check method.
	 * @param typeDecl the target type declaration whose assertion check
	 *                 methods are to be generated.
	 */
	public InvariantMethodAdviceAsPreconditionMethodClientAwareChecking(boolean isStatic, JmlTypeDeclaration typeDecl, VarGenerator varGen)
	{ 
		super(isStatic, typeDecl, varGen);
	}

	//	----------------------------------------------------------------------
	// GENERATION
	// ----------------------------------------------------------------------

	/** Generate and return a type-level assertion check method such
	 * as invariants and history constraints.  Append to the body
	 * (<code>stmt</code>): (1) code to check the inherited assertions
	 * if any, and (2) code to throw an appropriate exception to
	 * notify an assertion violation. 
	 * 
	 * @param stmt code to evaluate the assertions; the result is supposed
	 *             to be stored in the variable <code>VN_ASSERTION</code>. 
	 *             A <code>null</code> value means that no assertion is 
	 *             specified or the assertion is not executable.
	 */
	public JMethodDeclarationType generate(RacNode stmt)
	{
		return null;
	}

	public JMethodDeclarationType generate()
	{

		StringBuffer code = buildBeforeAdvice();
		code.append("\n");

		return RacParser.parseMethod(code.toString(), null);
	}

	/** Builds and returns the method header of the assertion check
	 * method as a string.
	 * 
	 */
	protected StringBuffer buildBeforeAdvice() 
	{

		// By Henrique Rebelo
		String classQualifiedName = AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName());
		String packageQualifiedName = this.typeDecl.getCClass().getJavaName().replace(this.typeDecl.ident(), "");	
		final StringBuffer code = new StringBuffer();
		final String HEADER = "@pre <File \\\""+this.typeDecl.ident()+".java\\\">";
		// defining error messages for visibility specs
		String errorMsgForPublicInstInv = "\"";
		String errorMsgForPublicStatInv = "\"";
		String errorMsgForProtectedInstInv = "\"";
		String errorMsgForProtectedStatInv = "\"";
		String errorMsgForDefaultInstInv = "\"";
		String errorMsgForDefaultStatInv = "\"";
		String errorMsgForPrivateInstInv = "\"";
		String errorMsgForPrivateStatInv = "\"";
		String evalErrorMsgForPublicInstInv = "\"";
		String evalErrorMsgForPublicStatInv = "\"";
		String evalErrorMsgForProtectedInstInv = "\"";
		String evalErrorMsgForProtectedStatInv = "\"";
		String evalErrorMsgForDefaultInstInv = "\"";
		String evalErrorMsgForDefaultStatInv = "\"";
		String evalErrorMsgForPrivateInstInv = "\"";
		String evalErrorMsgForPrivateStatInv = "\"";

		if (!this.getInvariantsTokenReference(false).equals("")){
			/*public invariant errors*/
			errorMsgForPublicInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPublicInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PUBLIC);
			errorMsgForPublicInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PUBLIC, varGen);
			errorMsgForPublicInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PUBLIC, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PUBLIC, varGen)+"\"":"");
			/*protected invariant errors*/
			errorMsgForProtectedInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForProtectedInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PROTECTED);
			errorMsgForProtectedInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PROTECTED, varGen);
			errorMsgForProtectedInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PROTECTED, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PROTECTED, varGen)+"\"":"");
			/*default invariant errors*/
			errorMsgForDefaultInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForDefaultInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, 0L);
			errorMsgForDefaultInstInv += this.getVisibilityContextValuesForInvariant(false, 0L, varGen);
			errorMsgForDefaultInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, 0L, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, 0L, varGen)+"\"":"");
			/*private invariant errors*/
			errorMsgForPrivateInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPrivateInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PRIVATE);
			errorMsgForPrivateInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PRIVATE, varGen);
			errorMsgForPrivateInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PRIVATE, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PRIVATE, varGen)+"\"":"");
			/*public invariant eval error*/
			evalErrorMsgForPublicInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPublicInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PUBLIC);
			evalErrorMsgForPublicInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PUBLIC, varGen);
			evalErrorMsgForPublicInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PUBLIC, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PUBLIC, varGen):"+\"");
			/*protected invariant eval error*/
			evalErrorMsgForProtectedInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForProtectedInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PROTECTED);
			evalErrorMsgForProtectedInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PROTECTED, varGen);
			evalErrorMsgForProtectedInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PROTECTED, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PROTECTED, varGen):"+\"");
			/*default invariant eval error*/
			evalErrorMsgForDefaultInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForDefaultInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, 0L);
			evalErrorMsgForDefaultInstInv += this.getVisibilityContextValuesForInvariant(false, 0L, varGen);
			evalErrorMsgForDefaultInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, 0L, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, 0L, varGen):"+\"");
			/*private invariant eval error*/
			evalErrorMsgForPrivateInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPrivateInstInv += ", " + this.getVisibilityInvariantsTokenReference(false, ACC_PRIVATE);
			evalErrorMsgForPrivateInstInv += this.getVisibilityContextValuesForInvariant(false, ACC_PRIVATE, varGen);
			evalErrorMsgForPrivateInstInv += (!this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PRIVATE, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PRIVATE, varGen):"+\"");
		}
		else{
			if(!this.getContextValuesForDefaultInvariant(false, varGen).equals("")){
				/*public invariant errors*/
				errorMsgForPublicInstInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForPublicInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false,ACC_PUBLIC, varGen) + "\"";
				/*protected invariant errors*/
				errorMsgForProtectedInstInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForProtectedInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false,ACC_PROTECTED, varGen) + "\"";
				/*default invariant errors*/
				errorMsgForDefaultInstInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForDefaultInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false,0L, varGen) + "\"";
				/*private invariant errors*/
				errorMsgForPrivateInstInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForPrivateInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false,ACC_PRIVATE, varGen) + "\"";
				/*public invariant eval error*/
				evalErrorMsgForPublicInstInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForPublicInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PUBLIC, varGen);
				/*protected invariant eval error*/
				evalErrorMsgForProtectedInstInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForProtectedInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PROTECTED, varGen);
				/*default invariant eval error*/
				evalErrorMsgForDefaultInstInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForDefaultInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false, 0L, varGen);
				/*private invariant eval error*/
				evalErrorMsgForPrivateInstInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForPrivateInstInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(false, ACC_PRIVATE, varGen);	
			}
		}

		if (!this.getInvariantsTokenReference(true).equals("")){
			/*public invariant errors*/
			errorMsgForPublicStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPublicStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PUBLIC);
			errorMsgForPublicStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PUBLIC, varGen);
			errorMsgForPublicStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen)+"\"":"");
			/*protected invariant errors*/
			errorMsgForProtectedStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForProtectedStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PROTECTED);
			errorMsgForProtectedStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PROTECTED, varGen);
			errorMsgForProtectedStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen)+"\"":"");
			/*default invariant errors*/
			errorMsgForDefaultStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForDefaultStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, 0L);
			errorMsgForDefaultStatInv += this.getVisibilityContextValuesForInvariant(true, 0L, varGen);
			errorMsgForDefaultStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen)+"\"":"");
			/*private invariant errors*/
			errorMsgForPrivateStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForPrivateStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PRIVATE);
			errorMsgForPrivateStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PRIVATE, varGen);
			errorMsgForPrivateStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen)+"\"":"");
			/*public invariant eval error*/
			evalErrorMsgForPublicStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPublicStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PUBLIC);
			evalErrorMsgForPublicStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PUBLIC, varGen);
			evalErrorMsgForPublicStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen):"+\"");
			/*protected invariant eval error*/
			evalErrorMsgForProtectedStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForProtectedStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PROTECTED);
			evalErrorMsgForProtectedStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PROTECTED, varGen);
			evalErrorMsgForProtectedStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen):"+\"");
			/*default invariant eval error*/
			evalErrorMsgForDefaultStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForDefaultStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, 0L);
			evalErrorMsgForDefaultStatInv += this.getVisibilityContextValuesForInvariant(true, 0L, varGen);
			evalErrorMsgForDefaultStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen):"+\"");
			/*private invariant eval error*/
			evalErrorMsgForPrivateStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForPrivateStatInv += ", " + this.getVisibilityInvariantsTokenReference(true, ACC_PRIVATE);
			evalErrorMsgForPrivateStatInv += this.getVisibilityContextValuesForInvariant(true, ACC_PRIVATE, varGen);
			evalErrorMsgForPrivateStatInv += (!this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen).equals("")? "+\"\\n"+this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen):"+\"");
		}
		else{
			if(!this.getContextValuesForDefaultInvariant(true, varGen).equals("")){
				/*public invariant errors*/
				errorMsgForPublicStatInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForPublicStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen) + "\"";
				/*protected invariant errors*/
				errorMsgForProtectedStatInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForProtectedStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen) + "\"";
				/*default invariant errors*/
				errorMsgForDefaultStatInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForDefaultStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen) + "\"";
				/*private invariant errors*/
				errorMsgForPrivateStatInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForPrivateStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen) + "\"";
				/*public invariant eval error*/
				evalErrorMsgForPublicStatInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForPublicStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PUBLIC, varGen);
				/*protected invariant eval error*/
				evalErrorMsgForProtectedStatInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForProtectedStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PROTECTED, varGen);
				/*default invariant eval error*/
				evalErrorMsgForDefaultStatInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForDefaultStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, 0L, varGen);
				/*private invariant eval error*/
				evalErrorMsgForPrivateStatInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForPrivateStatInv += "\\n" + this.getVisibilityContextValuesForDefaultInvariant(true, ACC_PRIVATE, varGen);
			}
		}

		// javadoc
		String javadocInst = "";
		String javadocStat = "";
		if (this.javadocInst != null) {
			javadocInst = this.javadocInst;
		} else {
			javadocInst = "/** Generated by AspectJML to check assertions. */";
		}
		if (this.javadocStat != null) {
			javadocStat = this.javadocStat;
		} else {
			javadocStat = "/** Generated by JML to check assertions. */";
		}
		//Rebelo - Only generate invariant checking method if there are invariants
		if((this.hasInstInv) || (this.hasStatInv)){
			boolean hasOther = false;

			if( (this.hasInstInv) && (this.hasStatInv)){

				// ************************** resolving static invariants **************************
				/*Public static invariants*/
				if(this.hasPublicStatInv){
					code.append("\n");
					code.append(javadocStat.replace("invariants", "public invariants"));
					code.append("\n");
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPublicStatInv, evalErrorMsgForPublicStatInv,
							this.publicStatInvPred, true, ACC_PUBLIC);
					hasOther = true;
				}
				/*Protected static invariants*/
				if(this.hasProtectedStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForProtectedStatInv, evalErrorMsgForProtectedStatInv,
							this.protectedStatInvPred, true, ACC_PROTECTED);
					hasOther = true;
				}
				/*Default static invariants*/
				if(this.hasDefaultStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "default invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "default invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForDefaultStatInv, evalErrorMsgForDefaultStatInv,
							this.defaultStatInvPred, true, 0L);
					hasOther = true;
				}
				/*Private static invariants*/
				if(this.hasPrivateStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "private invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "private invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPrivateStatInv, evalErrorMsgForPrivateStatInv,
							this.privateStatInvPred, true, ACC_PRIVATE);
					hasOther = true;
				}

				// ************************** resolving instance invariants **************************
				/*Public instance invariants*/
				if(this.hasPublicInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "public invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "public invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPublicInstInv, evalErrorMsgForPublicInstInv,
							this.publicInstInvPred, false, ACC_PUBLIC);
					hasOther = true;
				}
				/*Protected instance invariants*/
				if(this.hasProtectedInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForProtectedInstInv, evalErrorMsgForProtectedInstInv,
							this.protectedInstInvPred, false, ACC_PROTECTED);
					hasOther = true;
				}
				/*Default instance invariants*/
				if(this.hasDefaultInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "default invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "default invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForDefaultInstInv, evalErrorMsgForDefaultInstInv,
							this.defaultInstInvPred, false, 0L);
					hasOther = true;
				}
				/*Private instance invariants*/
				if(this.hasPrivateInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "private invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "private invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPrivateInstInv, evalErrorMsgForPrivateInstInv,
							this.privateInstInvPred, false, ACC_PRIVATE);
					hasOther = true;
				}
			}
			else if(this.hasInstInv){
				/*Public instance invariants*/
				if(this.hasPublicInstInv){
					code.append("\n");
					code.append(javadocInst.replace("invariants", "public invariants"));
					code.append("\n");
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPublicInstInv, evalErrorMsgForPublicInstInv,
							this.publicInstInvPred, false, ACC_PUBLIC);
					hasOther = true;
				}
				/*Protected instance invariants*/
				if(this.hasProtectedInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForProtectedInstInv, evalErrorMsgForProtectedInstInv,
							this.protectedInstInvPred, false, ACC_PROTECTED);
					hasOther = true;
				}
				/*Default instance invariants*/
				if(this.hasDefaultInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "default invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "default invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForDefaultInstInv, evalErrorMsgForDefaultInstInv,
							this.defaultInstInvPred, false, 0L);
					hasOther = true;
				}
				/*Private instance invariants*/
				if(this.hasPrivateInstInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocInst.replace("invariants", "private invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocInst.replace("invariants", "private invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPrivateInstInv, evalErrorMsgForPrivateInstInv,
							this.privateInstInvPred, false, ACC_PRIVATE);
					hasOther = true;
				}
			}
			else if(this.hasStatInv){
				/*Public static invariants*/
				if(this.hasPublicStatInv){
					code.append("\n");
					code.append(javadocStat.replace("invariants", "public invariants"));
					code.append("\n");
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPublicStatInv, evalErrorMsgForPublicStatInv,
							this.publicStatInvPred, true, ACC_PUBLIC);
					hasOther = true;
				}
				/*Protected static invariants*/
				if(this.hasProtectedStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "protected invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForProtectedStatInv, evalErrorMsgForProtectedStatInv,
							this.protectedStatInvPred, true, ACC_PROTECTED);
					hasOther = true;
				}
				/*Default static invariants*/
				if(this.hasDefaultStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "default invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "default invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForDefaultStatInv, evalErrorMsgForDefaultStatInv,
							this.defaultStatInvPred, true, 0L);
					hasOther = true;
				}
				/*Private static invariants*/
				if(this.hasPrivateStatInv){
					if(hasOther){
						code.append("\n");
						code.append("\n");
						code.append(javadocStat.replace("invariants", "private invariants"));
						code.append("\n");
					}
					else{
						code.append("\n");
						code.append(javadocStat.replace("invariants", "private invariants"));
						code.append("\n");
					}
					generateBeforeAdviceForInvChecking(classQualifiedName, packageQualifiedName, code,
							errorMsgForPrivateStatInv, evalErrorMsgForPrivateStatInv,
							this.privateStatInvPred, true, ACC_PRIVATE);
					hasOther = true;
				}
			}
		}	
		return code;
	}

	private void generateBeforeAdviceForInvChecking(String classQualifiedName, String packageQualifiedName,
			final StringBuffer code, String errorMsg,
			String evalErrorMsg, String predClause, boolean forStatic, long visibility) {
		
		String adviceexecution = "";
		if(AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)){
			adviceexecution = " || (adviceexecution())";
		}

		if (visibility == ACC_PUBLIC) {
			this.exceptionToThrow = "JMLPublicInvariantError";
		} else if (visibility == ACC_PROTECTED) {
			this.exceptionToThrow = "JMLProtectedInvariantError";
		} else if (visibility == 0L) { //default
			this.exceptionToThrow = "JMLDefaultInvariantError";
		} else if (visibility == ACC_PRIVATE) {
			this.exceptionToThrow = "JMLPrivateInvariantError";
		}
		
		// making static invariants inheritable to be checked on subtypes - hemr
//		String plus = (this.typeDecl.isInterface()? "+" : "");
		String plus = "+";
		if(forStatic){
			code.append("before (").append(")").append(" :");	
			code.append("\n");
			code.append("   (call( * "+classQualifiedName+plus+".*(..))").append(" || \n");
			code.append("     call("+classQualifiedName+plus+".new(..))").append(adviceexecution).append(")");
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append(" && \n");
				code.append("   !@annotation(JMLHelper)");
			}
		}
		else{
			code.append("before (final ").append(classQualifiedName).append(" ").append("object$rac");	
			code.append(")").append(" :");
			code.append("\n");
			code.append("   (call(!static * "+classQualifiedName+"+.*(..))").append(adviceexecution).append(")");
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append(" && \n");
				code.append("   !@annotation(JMLHelper)");
			}
		}
		
		code.append("&&");
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
		// adding JML quantifierInnerClasses if any
		code.append(this.getQuantifierInnerClasses(predClause));
		code.append("       String invErrorMsg = \""+errorMsg+";\n");
		code.append("       String evalErrorMsg = "+evalErrorMsg+"\\nCaused by: \";\n");
		code.append("       boolean rac$b = true;\n");
		code.append("       try {\n");
		code.append("        rac$b = "+predClause+";\n");
		code.append("       } catch (JMLNonExecutableException rac$nonExec) {\n");
		code.append("          rac$b = ").append(Main.aRacOptions.mustBeExecutable()).append(";\n");
		code.append("       } catch (Throwable rac$cause) {\n");
		code.append("        if(rac$cause instanceof JMLAssertionError) {\n");
		code.append("          throw (JMLAssertionError) rac$cause;\n");
		code.append("        }\n");
		code.append("        else {\n");
		code.append("          throw new JMLEvaluationError(evalErrorMsg + rac$cause);\n");
		code.append("        }\n");
		code.append("       }\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("     JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, "+visibility+");\n");
		}
		else{
			code.append("     JMLChecker.checkInvariant(rac$b, invErrorMsg, "+visibility+");\n");
		}
		code.append("\n").append("   }");
	}

	protected /*@ pure @*/ boolean canInherit() {
		// TODO Auto-generated method stub
		return false;
	}
}
