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
 * $Id: ConstraintMethod.java,v 1.0 2010/04/02 13:53:09 henriquerebelo Exp $
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

public class ConstraintMethod extends AssertionMethod {

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
	protected ConstraintMethod(boolean isStatic, 
			/*@ non_null @*/ JmlTypeDeclaration typeDecl, VarGenerator varGen) {
		this.exceptionToThrow = "JMLHistoryConstraintError";
		this.typeDecl = typeDecl;
		this.varGen = varGen;
		this.oldExprs = new ArrayList();
		this.oldExprsDecl = new ArrayList();
		this.oldExprsForStat = new ArrayList();
		this.oldExprsDeclForStat = new ArrayList();

		this.instConstPred = AspectUtil.changeThisOrSuperRefToAdviceRef(combineUniversalConstraints(false, this.varGen), typeDecl);
		this.statConstPred = combineUniversalConstraints(true, this.varGen);
		this.hasInstConst = !this.instConstPred.equals("");
		this.hasStatConst = !this.statConstPred.equals("");

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
		final StringBuffer code = new StringBuffer();
		final String HEADER = "@post <File \\\""+this.typeDecl.ident()+".java\\\">";
		String errorMsgForInstInv = "\"";
		String errorMsgForStatInv = "\"";
		String evalErrorMsgForInstInv = "\"\"";
		String evalErrorMsgForStatInv = "\"\"";

		if (!this.getConstraintTokenReference(false).equals("")){
			// JML Constraint Error
			errorMsgForInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForInstInv += ", " + this.getConstraintTokenReference(false);
			errorMsgForInstInv += this.getContextValuesForConstraint(false, this.varGen);

			// JML Evaluation Error
			evalErrorMsgForInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForInstInv += ", " + this.getConstraintTokenReference(false);
			evalErrorMsgForInstInv += this.getContextValuesForConstraint(false, this.varGen);
		}

		if (!this.getConstraintTokenReference(true).equals("")){
			// JML Constraint Error
			errorMsgForStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForStatInv += ", " + this.getConstraintTokenReference(true);
			errorMsgForStatInv += this.getContextValuesForConstraint(true, this.varGen);

			// JML Evaluation Error
			evalErrorMsgForStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForStatInv += ", " + this.getConstraintTokenReference(true);
			evalErrorMsgForStatInv += this.getContextValuesForConstraint(true, this.varGen);
		}

		//Rebelo - Only generate constraint checking method if there are constraints
		// Translating universal constraints
		if((this.hasInstConst) || (this.hasStatConst)){
			//heading if any c

			// handling universal constraints
			if((this.hasInstConst) && (this.hasStatConst)) {
				code.append("\n"); 
				code.append(this.javadoc);
				code.append("\n");
				this.generateAroundAdviceForUniversalConstraintChecking(classQualifiedName,
						code, errorMsgForInstInv, evalErrorMsgForInstInv, this.instConstPred, false);
				code.append("\n");
				code.append("\n");
				code.append(this.javadocStat);
				code.append("\n");
				this.generateAroundAdviceForUniversalConstraintChecking(classQualifiedName,
						code, errorMsgForStatInv, evalErrorMsgForStatInv, this.statConstPred, true);
			}
			else if(this.hasInstConst) {
				code.append("\n"); 
				code.append(this.javadoc);
				code.append("\n");
				this.generateAroundAdviceForUniversalConstraintChecking(classQualifiedName,
						code, errorMsgForInstInv, evalErrorMsgForInstInv, this.instConstPred, false);
			}
			else if(this.hasStatConst){
				code.append("\n");
				code.append(this.javadocStat);
				code.append("\n");
				this.generateAroundAdviceForUniversalConstraintChecking(classQualifiedName,
						code, errorMsgForStatInv, evalErrorMsgForStatInv, this.statConstPred, true);
			}
		}	

		// Translating specific constraints
		String specInstConst =  this.generateCodeForSpecificConstraintChecking(false, this.varGen);
		String specStatConst =  this.generateCodeForSpecificConstraintChecking(true, this.varGen);

		if((this.hasInstConst) || (this.hasStatConst)){
			code.append("\n");
		}

		if(!(specInstConst.equals("")) && (!specStatConst.equals(""))){
			code.append(specInstConst);
			code.append("\n");
			code.append(specStatConst);
		}
		else if (!specInstConst.equals("")){
			code.append(specInstConst);
		}
		else if (!specStatConst.equals("")){
			code.append(specStatConst);
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
			String classQualifiedName, final StringBuffer code,
			String errorMsg, String evalErrorMsg, String constPred, boolean forStatic) {
		
		String adviceexecution = "";
		if(AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)){
			adviceexecution = " || (adviceexecution())";
		}
		
		code.append("Object around (final ").append(classQualifiedName).append(" ").append("object$rac");	
		code.append(")").append(" :");
		code.append("\n");
		
		// making static constraints inheritable to be checked on subtypes - hemr
		if(forStatic){
			code.append("   (execution(* "+classQualifiedName+"+.*(..))");
			code.append(" || ");
			code.append("\n");	
			if(this.typeDecl.getCClass().isAbstract()){
				code.append("   (execution("+classQualifiedName+"+.new(..))").append(" && !within("+classQualifiedName+"))").append(adviceexecution).append(")");
			}
			else{
				code.append("   execution("+classQualifiedName+"+.new(..))").append(adviceexecution).append(")");
			}
			code.append(" && ");
			code.append("\n");	
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append("   !@annotation(JMLHelper)");
				code.append(" && ");
				code.append("\n");	
			}
		}
		else{
			code.append("   (execution(!static * "+classQualifiedName+"+.*(..))").append(" && \n");	
			code.append("   !execution(void "+classQualifiedName+".finalize() throws Throwable)").append(adviceexecution).append(")");
			code.append(" && ");
			code.append("\n");	
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				code.append("   !@annotation(JMLHelper)");
				code.append(" && ");
			}
		}
		code.append("\n");
		code.append("   this(object$rac)");
		code.append(" {\n");
		code.append("    ").append("Object").append(" ").append("rac$result");
		code.append(" = ").append("null").append(";\n");
		// when calling super we should check static inv... so the following lines should remain commented
//		if(forStatic){
//			code.append("    if (object$rac.getClass() == ").append(classQualifiedName).append(".class)");
//			code.append(" {\n");
//		}
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
				code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
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
				code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
				code.append("     }");
				code.append("\n");
			}	
		}
		code.append("    boolean rac$b = true;\n");
		code.append("    try {\n");
		code.append("      ").append("rac$result = proceed(object$rac)").append(";").append("//executing the method\n");
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
			code.append("       JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", -1);");
		}
		else{
			code.append("       JMLChecker.checkConstraint(rac$b, \""+errorMsg+", -1);");
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
		code.append("             }\n");
		code.append("             else {\n");
		code.append("              throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("             }\n");
		code.append("           }\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("           JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", -1);");
		}
		else{
			code.append("           JMLChecker.checkConstraint(rac$b, \""+errorMsg+", -1);");
		}
		code.append("         } catch (Throwable rac$cause)");
		code.append(" {\n");
		code.append("             if (rac$cause instanceof JMLHistoryConstraintError) {\n");
		code.append("               throw (JMLHistoryConstraintError) rac$e;\n");
		code.append("             }\n");
		code.append("             else {\n");
		code.append("               throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("             }");
		code.append("\n").append("         ").append("}");
		code.append("\n");
		code.append("         if (rac$e instanceof Throwable) {\n");
		code.append("          throw new JMLInternalRuntimeException(rac$e);\n");
		code.append("         }\n");
		code.append("\n").append("       }");
		code.append("\n");
		code.append("    ").append("return rac$result;");
		code.append("\n").append("   }");
	}

	private void generateAroundAdviceForSpecificConstraintChecking(
			String classQualifiedName, final StringBuffer code,
			String errorMsg, String evalErrorMsg, String constPred, String [] methodNames, boolean forStatic) {

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
				  code.append((methodNames[i].contains("new")? "   (execution("+classQualifiedName+"."+methodNames[i]+")" : "   (execution(* "+classQualifiedName+"."+methodNames[i]+")"));
			}	
			else if((i == 0) && (methodNames.length == 1)){				
			  code.append((methodNames[i].contains("new")? "   execution("+classQualifiedName+"."+methodNames[i]+")" : "   execution(* "+classQualifiedName+"."+methodNames[i]+")"));
			}
			else {
				code.append(" || ");
				code.append("\n");
				code.append((methodNames[i].contains("new")? "   execution("+classQualifiedName+"."+methodNames[i]+")" : "   execution(* "+classQualifiedName+"."+methodNames[i]+")"));	
			}
			if((i == (methodNames.length-1)) && (methodNames.length > 1)){
				  code.append(")");
			}	  
		}
		// making static constraints inheritable to be checked on subtypes - hemr
		if (!forStatic){
			code.append(" && ");
			code.append("\n");
			code.append("   this(object$rac)");			
		}
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
				code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
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
				code.append("           throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
				code.append("     }");
				code.append("\n");
			}	
		}
		code.append("    boolean rac$b = true;\n");
		code.append("    try {\n");
		if(forStatic){
			code.append("      ").append("rac$result = proceed()").append(";").append("//executing the method\n");
		}
		else{
			code.append("      ").append("rac$result = proceed(object$rac)").append(";").append("//executing the method\n");	
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
			code.append("      JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", -1);");
		}
		else{
			code.append("      JMLChecker.checkConstraint(rac$b, \""+errorMsg+", -1);");
		}
		code.append("\n").append("    ").append(" }");
		code.append(" catch (Throwable rac$e) {\n");
		code.append("         if(rac$e instanceof JMLEvaluationError){\n");
		code.append("          throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$e);\n");
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
		code.append("             }\n");
		code.append("             else {\n");
		code.append("              throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("             }\n");
		code.append("           }\n");
		if(Main.aRacOptions.multipleSpecCaseChecking()){
			code.append("           JMLChecker.checkConstraintMultipleSpecCaseChecking(rac$b, \""+errorMsg+", -1);");
		}
		else{
			code.append("           JMLChecker.checkConstraint(rac$b, \""+errorMsg+", -1);");
		}
		code.append("         } catch (Throwable rac$cause)");
		code.append(" {\n");
		code.append("             if (rac$cause instanceof JMLHistoryConstraintError) {\n");
		code.append("               throw (JMLHistoryConstraintError) rac$e;\n");
		code.append("             }\n");
		code.append("             else {\n");
		code.append("               throw new JMLEvaluationError("+evalErrorMsg+"+\"\\nCaused by: \""+"+rac$cause);\n");
		code.append("             }");
		code.append("\n").append("         ").append("}");
		code.append("\n");
		code.append("         if (rac$e instanceof Throwable) {\n");
		code.append("          throw new JMLInternalRuntimeException(rac$e);\n");
		code.append("         }\n");
		code.append("\n").append("       }");
		code.append("\n");
		code.append("    ").append("return rac$result;");
		code.append("\n").append("   }");
	}

	private String combineUniversalConstraints(boolean forStatic, VarGenerator varGen){
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
			if (!isCheckable(constraints[i]) ||
					hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
				continue;

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
				this.hasOldExpressionsForStat = transConstraint.oldExprs().size() > 0;
				this.oldExprsForStat.addAll(transConstraint.oldExprs());
				this.oldExprsDeclForStat.addAll(transConstraint.oldVarDecl());
			}
			else{
				this.hasOldExpressions = transConstraint.oldExprs().size() > 0;
				this.oldExprs.addAll(transConstraint.oldExprs());
				this.oldExprsDecl.addAll(transConstraint.oldVarDecl());	
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

	private String generateCodeForSpecificConstraintChecking(boolean forStatic, VarGenerator varGen){
		final StringBuffer code = new StringBuffer("");
		String classQualifiedName = this.typeDecl.getCClass().getJavaName();
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
			if (!isCheckable(constraints[i]) ||
					hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
				continue;

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
				if(forStatic)
					code.append(this.javadocStat);
				else
					code.append(this.javadoc);
				code.append("\n");
				this.generateAroundAdviceForSpecificConstraintChecking(
						classQualifiedName, code, errorMsg, evalErrorMsg,
						constPred, this.getMethodNames(constraints[i]
						                                           .methodNames().methodNameList()), forStatic);
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

	private String instConstPred = "";
	private String statConstPred = "";
	private boolean hasInstConst;
	private boolean hasStatConst;

	private boolean hasOldExpressions;
	private boolean hasOldExpressionsForStat;
	private List oldExprs;
	private List oldExprsDecl;
	private List oldExprsForStat;
	private List oldExprsDeclForStat;
}

