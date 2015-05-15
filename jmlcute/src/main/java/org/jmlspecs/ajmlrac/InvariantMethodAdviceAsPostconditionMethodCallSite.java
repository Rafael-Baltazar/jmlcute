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
 * $Id: InvariantMethodAdviceAsPostconditionMethodCallSite.java,v 1.0 2013/08/1 11:50:15 henriquerebelo Exp $
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
public class InvariantMethodAdviceAsPostconditionMethodCallSite extends InvariantLikeMethod{
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
	public InvariantMethodAdviceAsPostconditionMethodCallSite(boolean isStatic, JmlTypeDeclaration typeDecl, VarGenerator varGen)
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
		StringBuffer code = buildAfterAdvice();
		code.append("\n");

		return RacParser.parseMethod(code.toString(), null);
	}

	/** Builds and returns the method header of the assertion check
	 * method as a string.
	 * 
	 */
	protected StringBuffer buildAfterAdvice() 
	{

		// By Henrique Rebelo
		String classQualifiedName = AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName());		
		final StringBuffer code = new StringBuffer();
		final String HEADER = "@post <File \\\""+this.typeDecl.ident()+".java\\\">";
		String errorMsgForInstInv = "\"";
		String errorMsgForStatInv = "\"";
		String evalErrorMsgForInstInv = "\"\"";
		String evalErrorMsgForStatInv = "\"\"";

		if (!this.getInvariantsTokenReference(false).equals("")){
			// JML Invariant Error
			errorMsgForInstInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForInstInv += ", " + this.getInvariantsTokenReference(false);
			errorMsgForInstInv += this.getContextValuesForInvariant(false, varGen);
			errorMsgForInstInv += (!this.getContextValuesForDefaultInvariant(true, varGen).equals("")? "+\"\\n"+this.getContextValuesForDefaultInvariant(false, varGen)+"\"":"");
			// JML Evaluation Error
			evalErrorMsgForInstInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForInstInv += ", " + this.getInvariantsTokenReference(false);
			evalErrorMsgForInstInv += this.getContextValuesForInvariant(false, varGen);
			evalErrorMsgForInstInv += (!this.getContextValuesForDefaultInvariant(false, varGen).equals("")? "+\"\\n"+this.getContextValuesForDefaultInvariant(false, varGen):"+\"");
		}
		else{
			if(!this.getContextValuesForDefaultInvariant(false, varGen).equals("")){
				// JML Invariant Error
				errorMsgForInstInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForInstInv += "\\n" + this.getContextValuesForDefaultInvariant(false, varGen) + "\"";
				// JML Evaluation Error
				evalErrorMsgForInstInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForInstInv += "\\n" + this.getContextValuesForDefaultInvariant(false, varGen);
			}
		}

		if (!this.getInvariantsTokenReference(true).equals("")){
			// JML Invariant Error
			errorMsgForStatInv = HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			errorMsgForStatInv += ", " + this.getInvariantsTokenReference(true);
			errorMsgForStatInv += this.getContextValuesForInvariant(true, varGen);
			errorMsgForStatInv += (!this.getContextValuesForDefaultInvariant(true, varGen).equals("")? "+\"\\n"+this.getContextValuesForDefaultInvariant(true, varGen)+"\"":"");
			// JML Evaluation Error
			evalErrorMsgForStatInv = SPEC_EVAL_ERROR_MSG + HEADER + SPEC_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
			evalErrorMsgForStatInv += ", " + this.getInvariantsTokenReference(true);
			evalErrorMsgForStatInv += this.getContextValuesForInvariant(true, varGen);
			evalErrorMsgForStatInv += (!this.getContextValuesForDefaultInvariant(true, varGen).equals("")? "+\"\\n"+this.getContextValuesForDefaultInvariant(true, varGen):"+\"");
		}
		else{
			if(!this.getContextValuesForDefaultInvariant(true, varGen).equals("")){
				// JML Invariant Error
				errorMsgForStatInv = HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				errorMsgForStatInv += "\\n" + this.getContextValuesForDefaultInvariant(true, varGen) + "\"";
				// JML Evaluation Error
				evalErrorMsgForStatInv = SPEC_EVAL_ERROR_MSG + HEADER + CODE_ERROR_MSG + "File \\\""+this.typeDecl.ident()+".java\\\"";
				evalErrorMsgForStatInv += "\\n" + this.getContextValuesForDefaultInvariant(true, varGen);
			}
		}

		//Rebelo - Only generate invariant checking method if there are invariants
		if((this.hasInstInv) || (this.hasStatInv)){
			String adviceexecution = "";
			if(AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)){
				adviceexecution = "\n ||    (adviceexecution())";
			}
			//heading if any c
			code.append("\n"); 
			if (this.javadoc != null) {
				code.append(this.javadoc);
			} else {
				code.append("/** Generated by AspectJML to check assertions. */");
			}
			code.append("\n");
			String instanceInvariantPredicateClause = this.instInvPred;
			String staticInvariantPredicateClause = this.statInvPred;

			if( (this.hasInstInv) && (this.hasStatInv)){
				code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");	
				code.append(")").append(" :");
				code.append("\n");
				code.append("   (call(!static * *(..))").append(adviceexecution).append(")").append(" && \n");
				code.append("   !call(void finalize() throws Throwable)");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
				code.append("   target(object$rac)");
				code.append(" && ");
				code.append("\n");
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(instanceInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForInstInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForInstInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+instanceInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     }");
				code.append("\n");
				code.append("\n").append("   }");
				code.append("\n");
				// handling constructors on return --- [[[hemr]]]
				// since this is a call pointcut, we need a extra after advice
				// we use a after returning advice
				code.append("after () returning (final ").append(classQualifiedName).append(" ").append("object$rac");	
				code.append(")").append(" :");
				code.append("\n");
				code.append("   call(new(..))");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(instanceInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForInstInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForInstInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+instanceInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     }");
				code.append("\n");
				code.append("\n").append("   }");
				code.append("\n");
				code.append("\n");
				code.append(this.javadocStat);
				code.append("\n");
				code.append("after (").append(")").append(" :");
				code.append("\n");
				
				// making static invariants inheritable to be checked on subtypes - hemr
				code.append("   (call( * "+classQualifiedName+"+.*(..))").append(" || \n");
				code.append("     call("+classQualifiedName+"+.new(..))").append(" || \n");
				code.append("     staticinitialization("+classQualifiedName+"+)").append(adviceexecution).append(")");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");		
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(staticInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForStatInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForStatInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+staticInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     }");
				code.append("\n");
				code.append("\n").append("   }");
			}
			else if(this.hasInstInv){
				code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");	
				code.append(")").append(" :");
				code.append("\n");
				code.append("   (call(!static * *(..))").append(adviceexecution).append(")").append(" && \n");
				code.append("   !call(void finalize() throws Throwable)");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
				code.append("   target(object$rac)");
				code.append(" && ");
				code.append("\n");
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(instanceInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForInstInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForInstInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+instanceInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     ").append("}");
				code.append("\n").append("   }");
				code.append("\n");
				// handling constructors on return --- [[[hemr]]]
				// since this is a call pointcut, we need a extra after advice
				// we use a after returning advice
				code.append("after () returning (final ").append(classQualifiedName).append(" ").append("object$rac");	
				code.append(")").append(" :");
				code.append("\n");
				code.append("   call(new(..))");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(instanceInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForInstInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForInstInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+instanceInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     }");
				code.append("\n");
				code.append("\n").append("   }");
			}
			else if(this.hasStatInv){
				code.append("after (");	
				code.append(")").append(" :");
				code.append("\n");
				
				// making static invariants inheritable to be checked on subtypes - hemr
				code.append("   (call( * "+classQualifiedName+"+.*(..))").append(" || \n");
				code.append("     call("+classQualifiedName+"+.new(..))").append(" || \n");
				code.append("     staticinitialization("+classQualifiedName+"+)").append(adviceexecution).append(")");
				code.append(" && ");
				code.append("\n");	
				if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
					code.append("   !@annotation(JMLHelper)");
					code.append(" && ");
					code.append("\n");	
				}
			    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
				code.append(" {\n");
				code.append("     if (!(JMLChecker.hasAnyJMLError))");
				code.append(" {\n");
				// adding JML quantifierInnerClasses if any
				code.append(this.getQuantifierInnerClasses(staticInvariantPredicateClause));
				code.append("       String invErrorMsg = \""+errorMsgForStatInv+";\n");
				code.append("       String evalErrorMsg = "+evalErrorMsgForStatInv+"\\nCaused by: \";\n");
				code.append("       boolean rac$b = true;\n");
				code.append("       try {\n");
				code.append("        rac$b = "+staticInvariantPredicateClause+";\n");
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
					code.append("       JMLChecker.checkInvariantMultipleSpecCaseChecking(rac$b, invErrorMsg, -1);\n");
				}
				else{
					code.append("       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);\n");
				}
				code.append("\n").append("     ").append("}");
				code.append("\n").append("   }");
				code.append("\n");
				code.append("\n");
			}
		}			
		return code;
	}

	protected /*@ pure @*/ boolean canInherit() {
		// TODO Auto-generated method stub
		return false;
	}
}
