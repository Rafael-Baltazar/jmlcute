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
 * $Id: Main.java,v 1.0 2009/02/20 16:48:06 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: TransType.java,v 1.74 2007/02/03 02:04:50 delara Exp $
 * by Frederic Rioux (based on Yoonsik Cheon's work)
 */

package org.jmlspecs.ajmlrac;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.jmlspecs.checker.JmlFieldDeclaration;
import org.jmlspecs.checker.JmlMessages;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlRepresentsDecl;
import org.jmlspecs.checker.JmlSourceClass;
import org.jmlspecs.checker.JmlSourceField;
import org.jmlspecs.checker.JmlSpecExpression;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CField;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JUnaryPromote;

/**
 * <p> An abstract class for translating JML type declarations.  The
 * translation may produce (1) a set of assertion check methods and
 * supporting fields (e.g., to hold old values) for classes, and (2)
 * for an interface declaration, a surrogate class as a static inner
 * class.</p> 
 *
 * <p> This class implements the <em>Template Method
 * Pattern</em> [GoF94]. The main template method is
 * <code>translate</code> which deines the major flow of control and
 * calls such translation methods as: 
 *
 * <ul> 
 * <li><code>translateInvariant<code/></li> 
 * <li><code>translateConstraint<code/></li>
 * <li><code>translateRepresents<code/></li> 
 * <li><code>translateBody<code/></li> 
 * <li><code>finalizeTranslation<code/></li> 
 * </ul>
 * 
 * Some methods are abstract and others are concrete. 
 * They may be refined by concrete subclasses such as
 * {@link TransClass} and {@link TransInterface}.
 *
 * <p> (David Cok): THIS IS NOT UP TO DATE The original code (which is
 * intact) has been embellished to handle the situation in which
 * source code is not available to be used to generate new java code
 * containing runtime assertion checks.  This is the case, for
 * example, in checking the assertions of classes in java.* .  This
 * situation obtains when the assertion check code is being generated
 * from a non-.java file and the object being tested is a class, not
 * an interface.  In this case the variable genSpecTestFile is set
 * true, and the generated code is produced as follows.  (If
 * genSpecTestFile==false, the original rewrite-the-java-file
 * mechanism is used unchanged.)
 *
 * <p> The generated class must be different from the class under
 * test, since it cannot replace it.  We presume that we cannot add to
 * the package of the class under test either, and in any case it is
 * convenient to have the generated class have the same name as the
 * class under test (convenient for generating test code).  Thus we
 * use the same class name but a different package for the generated
 * class.  For clarity, we will call the class under test class p.C
 * and the generated class testspecs.p.C .  The actual generated class
 * name is determined by the --packageName option.
 *
 * <p> There are two subcases.  One in which we generate a subclass of
 * p.C, which is called Wrapper, and one in which we do not generate
 * such a subclass.  The variable genWrapperClass is true in the first
 * case, false in the second.
 *
 * <ul> <li> genWrapperClass must be true if there are any protected
 * methods, fields, or constructors that must be tested or are used in
 * specifications.
 *
 * <li>
 * genWrapperClass must be false if the class p.C is final
 *
 * <li> genWrapperClass must be false if the class p.C has only
 * or private constructors 
 *
 * <li> genWrapperClass must be false if the class p.C has fields that
 * are of type p.C (e.g. BigInteger.ZERO, Double.MAX_INTEGER) because
 * we have not implemented any mechanisms to convert a p.C object to a
 * Wrapper object.  Although straightforward for BigInteger and
 * Double, it would need to rely on the presence of a copy
 * constructor.  Hence we just forbid a Wrapper class in this case.
 *
 * <li> If a protected method of p.C is final, we are stuck - we
 * cannot test or access this method.  </ul>
 *
 * <p> We generate testspecs.p.C with the following content.
 * 
 * <ul> <li> - All methods that check specifications are members of
 * the generated class, as they are in the case of
 * genSpecTestFile==false, but some field or method access may be
 * different.
 *
 * <li> - (genWrapperClass==true): A static public nested class named
 * Wrapper which has p.C as a super class and with content as
 * described in the following.
 *	
 * <li> - A field named delegee of type p.C if genWrapperClass==false
 * of type Wrapper if genWrapperClass==true
 *
 * <li> - Members of p.C with package or private access are not
 * available and cannot be tested.  If specifications need to access
 * these members, it may not be possible to test the class.
 *	
 * <li> - For each public method m of p.C: a public method m in
 * testspecs.p.C is generated (even with genSpecTestFile false) that
 * checks specifications appropriately, calling internal$m(...) as
 * needed.  When genSpecTestFile==true, internal$m is modified to call
 * delegee.m(...)  
 *
 * <li> - For each protected method m of p.C: [must have
 * genWrapperClass==true] a public method m in testspecs.p.C is
 * *generated (even with genSpecTestFile false) that checks
 * *specifications appropriately, calling internal$m(...) as needed.
 * *When genSpecTestFile==true, internal$m is modified to call
 * *delegee.m(...)  Also generate a public method in Wrapper with the
 * *same name and arguments that simply calls/returns super.m(...).
 * *Note: If there are any such protected methods of p.C, then
 * *genWrapperClass must be true, since testspecs.p.C will not be able
 * *to call p.C.m .
 * 
 * <li> - For each public constructor of p.C: If
 * (genWrapperClass==false) generate a public constructor in
 * testspecs.p.C that checks specifications appropriately, calling new
 * p.C(...) as needed.  If (genWrapperClass==true) generate a public
 * constructor in testspecs.p.C that checks specifications
 * appropriately, calling new Wrapper(...) as needed and generate a
 * public constructor in Wrapper with the same name and arguments that
 * simply calls super(...)  
 * 
 * <li> - For each protected constructor of
 * p.C: [Must have genWrapperClass==true] generate a public
 * constructor in testspecs.p.C that checks specifications
 * appropriately, calling new Wrapper(...) as needed.  And if
 * (genWrapperClass==true) generate a public method in Wrapper with
 * the same name and arguments that simply calls/returns super(...)
 * [not strictly needed for public methods of p.C].
 *	
 * <li> - there are no public or protected constructors of p.C then
 * genWrapperClass must be false.  We then add one constructor to
 * testspecs.p.C of the form
 *	
 * public C(p.C o) { delegee = o; }  [genWrapperClass==false]
 *	
 * public C(Wrapper o) { delegee = o; }  [genWrapperClass==true]
 *
 * <li> If p.C has only a default constructor, then testspecs.p.C is
 * given a constructor with no arguments that simply sets delegee ==
 * new p.C();
 *
 * <li> - For each public field f of p.C: If
 * (genWrapperClass==false) references to the field in specifications
 * are changed to delegee.f If (genWrapperClass==true) generate a
 * public method in Wrapper named spec$f$C that simply returns the
 * value of the field.  References to the field in specifications will
 * call delegee.spec$f$C().  [ In this latter case, we could use
 * delegee.f, but we do it this way to be consistent with the
 * mechanism for protected fields.]
 *
 * <li> - For each protected field f of p.C: [Must have
 * genWrapperClass==true] generate a public method in Wrapper named
 * spec$f$C that simply returns the value of the field.  Any
 * references to the field in specifications will call
 * delegee.spec$f$C().
 *
 * <li> - Creating objects for testcases.  The receivers need to be of
 * type testspecs.p.C.  Other objects used as arguments should be of
 * dynamic type Wrapper (if getWrapperClass is true) otherwise of type
 * p.C .  
 * </ul> </p>
 *
 * @author Yoonsik Cheon
 * @author David Cok
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 *
 * @see TransClass
 * @see TransInterface
 */

public abstract class TransType extends TransUtils {

	/** true if we are operating on spec files */
	static public boolean genSpecTestFile = false;
	static public boolean genWrapperClass = false;
	// FIXME - must refactor to find a better way to communicate the
	// above information to other classes than by these global
	// variables - DRC.

	// static public TransContext transContext = null;

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Constructs a <code>TransType</code> object.
	 *
	 * @param typeDecl target type declaration to be translated
	 *
	 * <pre><jml>
	 * requires typeDecl != null;
	 * </jml></pre>  
	 */
	protected TransType(JmlTypeDeclaration typeDecl) {
		this.typeDecl = typeDecl;
		//this.transContext = new TransContext();
		TransUtils.typeDecl = typeDecl;

		genSpecTestFile = Main.isSpecMode(typeDecl) &&
		// jmlc compiles .spec files
		!((JmlSourceClass) typeDecl.getCClass()).inSpecFile();

		genWrapperClass = false;

		if (genSpecTestFile) {
			prepareSpecTestFile();
		}

		currentCClass = typeDecl.getCClass();
		varGen = VarGenerator.forClass();
		TransUtils.initIncludedInInheritance(currentCClass);
	}

	private void prepareSpecTestFile() {
		// set this to the default in the case of genSpecTestFile = true
		genWrapperClass = true; 
		// All should work either way.
		boolean mustBeTrue = false;
		boolean mustBeFalse = false;
		//System.out.println("A " + mustBeTrue + " " + mustBeFalse);

		// If the class under test is final, we cannot generate a
		// Wrapper derived class
		if (typeDecl.getCClass().isFinal()) {
			mustBeFalse = true;
		}
		//System.out.println("B " + mustBeTrue + " " + mustBeFalse);

		// If the class under test has no public or protected
		// constructors, we cannot generate a Wrapper derived
		// class If the class under test has a protected method,
		// we must generate a Wrapper derived class
		boolean anyPublicProtectedConstructors = false;
		boolean someConstructor = false;
//		for (Iterator ii = typeDecl.methods().iterator(); ii.hasNext(); ) {
//			JMethodDeclarationType jm = 
//				(JMethodDeclarationType)(ii.next());
//			if (hasFlag(jm.modifiers(),ACC_PROTECTED)) {
//				mustBeTrue = true;
//			}
//			if (jm instanceof JConstructorDeclarationType) {
//				someConstructor = true;
//			}
//			if (jm instanceof JConstructorDeclarationType &&
//					hasFlag(jm.modifiers(),ACC_PROTECTED|ACC_PUBLIC)) {
//				anyPublicProtectedConstructors = true;
//			}
//		} // for

		if (someConstructor && !anyPublicProtectedConstructors) {
			mustBeFalse = true;
		}
		//System.out.println("C " + mustBeTrue + " " + mustBeFalse);

		// If the class under test has a protected field, we must
		// generate a Wrapper derived class If the class under
		// test has field whose type is that of the class, then we
		// cannot generate a Wrapper derived class (because we
		// haven't implemented that case - it needs a way to
		// rewrap the object in a Wrapper)
		JPhylum[] f = typeDecl.fieldsAndInits();
		for (int ii = 0; ii<f.length; ++ii) {
			if (!(f[ii] instanceof JFieldDeclarationType)) {
				continue;
			}
			JFieldDeclarationType jt = (JFieldDeclarationType)(f[ii]);
			if (hasFlag(jt.modifiers(),ACC_PROTECTED)) {
				mustBeTrue = true;
			}
			if (jt.getType().equals(typeDecl.getCClass().getType())) 
				mustBeFalse = true;
		}
		//System.out.println("D " + mustBeTrue + " " + mustBeFalse);
		if (hasFlag(typeDecl.modifiers(),ACC_ABSTRACT)) { 
			mustBeTrue = false; mustBeFalse = true; 
		}
		//System.out.println("E " + mustBeTrue + " " + mustBeFalse);

		if (mustBeTrue && mustBeFalse) {
			System.out.println("CANNOT GENERATE A WORKING TEST CLASS FOR "
					+ typeDecl.getCClass().toString());
			// FIXME -- generate an error
		} else {
			if (mustBeTrue) genWrapperClass = true;
			if (mustBeFalse) genWrapperClass = false;
		}
		//System.out.println("TEST CLASS " + 
		//typeDecl.getCClass().toString() + " genWrapper=" + 
		//genWrapperClass);
	}

	// ----------------------------------------------------------------------
	// TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translates the given type declaration. The translation may produce
	 * a collection of assertion check methods.
	 */
	public void translate() 
	{

		// translate type decl if it is not a model
		if (hasFlag(typeDecl.modifiers(), ACC_MODEL))
			return;

		ArrayList methods = new ArrayList(typeDecl.methods());
		ArrayList inners = typeDecl.inners();
		// adding inner methods - [[[hemr]]]
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				methods.addAll(currentInnerType.methods());
			}
		}
		JPhylum[] fieldsAndInits = typeDecl.fieldsAndInits();

		// translate represents clauses. 
		// WARNING! The translation of represents clauses must precede
		// that of body which also performs the translation of
		// model fields if any.
		// The reason is that if this type declaration contains both
		// a model field declaration and its represents clause, 
		// the model field access method should be generated from the
		// represents clause, not from the model field declaration
		// (see translateRepresents and translateField).
		if(Main.ajWeaver != null){
			Main.aRacOptions.set_ajWeaver(Main.ajWeaver);
		}
		if (!Main.aRacOptions.ajWeaver().startsWith("abc")){
			this.markHelperMethods(methods);	
		}
		this.translateModelFields(typeDecl.getCClass().fields());
		// translating inner model fields - [[[hemr]]]
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				this.translateModelFields(currentInnerType.getCClass().fields());
			}
		}
		
//		if(AspectUtil.getInstance().getInterfaceStaticModelFields().size() > 0){
//			StringBuffer code = new StringBuffer("");
//			code.append("\n/** Generated by JML to implement the static model fields of interface "+typeDecl.ident()+"*/\n");
//			code.append("public interface InternalJmlSurrogate_"+typeDecl.ident()).append("{\n");
//			code.append("  public class JmlSurrogate_"+typeDecl.ident()+"{\n");
//			for (Iterator iterator = AspectUtil.getInstance().getInterfaceStaticModelFields().iterator(); iterator.hasNext();) {
//				String currentField = (String) iterator.next();
//				code.append("    "+currentField);
//			}
//			code.append("  }\n");
//			code.append("}\n");
//			code.append("declare parents: "+typeDecl.getCClass().getJavaName()+" extends InternalJmlSurrogate_"+typeDecl.ident()+";");
//			code.append("\n");
//	    	typeDecl.addMember(RacParser.parseMethod(code.toString()));
//	    	AspectUtil.getInstance().emptyInterfaceStaticModelFields();
//		}
		this.translateRepresents(typeDecl.representsDecls());
		// translating inner represents decls - [[[hemr]]]
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				this.translateRepresents(currentInnerType.representsDecls());
			}
		}
		
		// translate body (i.e., inner classes, field, and methods)
		translateBody(inners, methods, fieldsAndInits);
		
		// add newly created postconditions methods (after) if any
		Iterator iter = AspectUtil.getInstance().getPostconditionNewMethodsAfterAdvice().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		//  for XCS
		// add newly created postconditions methods (after) if any
		iter = AspectUtil.getInstance().getPostconditionNewMethodsAfterAdviceXCS().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		// translate invariants and (history) constraints.
		this.translateInvariantAsPrecondition();
		
		// add newly created preconditions methods if any
		iter = AspectUtil.getInstance().getPreconditionNewMethodsAdvice().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		// for XCS
		iter = AspectUtil.getInstance().getPreconditionNewMethodsAdviceXCS().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		// due to AspectJ precedence, history constraints implemented as around must be declared before other existing around (if any)
		this.translateConstraint();
		
		// add newly created postconditions methods (around) if any
		iter = AspectUtil.getInstance().getPostconditionNewMethodsAroundAdvice().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		// for XCS
		iter = AspectUtil.getInstance().getPostconditionNewMethodsAroundAdviceXCS().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		
		this.translateInvariantAsPostcondition();
		
		String adviceexecution = "";
		if(AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)){
			adviceexecution = " || (adviceexecution() && within("+AspectUtil.replaceDollaSymbol(typeDecl.getCClass().getJavaName())+"+))";
		}
		
		if(AspectUtil.getInstance().isCompilationUnitRacable){
			StringBuffer code = new StringBuffer();
			
			if(AspectUtil.getInstance().getExceptionsInSignalsClausesInCompilationUnit().size() > 0){
				code.append("\n");
				code.append("/** Generated by AspectJML to recover checked exceptions. *\n");
				code.append("  *  This is based on the exception introduction pattern by Laddad. */\n");
				for (Iterator iterator = AspectUtil.getInstance().getExceptionsInSignalsClausesInCompilationUnit().iterator(); iterator.hasNext();) {
					CType cType = (CType) iterator.next();
					String pc = "";
					if(Main.aRacOptions.clientAwareChecking()){
						pc = "(call(* "+this.typeDecl.getCClass().getJavaName()+"+.*(..)"+" throws "+cType.toString()+")" + " ||\n" 
						         + "    call("+this.typeDecl.getCClass().getJavaName()+"+.new(..)"+" throws "+cType.toString()+"))";
					}
					else{
						if(Main.aRacOptions.callSiteInstrumentation()){
							pc = "(call(* "+this.typeDecl.getCClass().getJavaName()+"+.*(..)"+" throws "+cType.toString()+")" + " ||\n" 
							         + "    call("+this.typeDecl.getCClass().getJavaName()+"+.new(..)"+" throws "+cType.toString()+"))";
						}
						if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
							if(pc.equals("")){
								pc = "(execution(* "+this.typeDecl.getCClass().getJavaName()+"+.*(..)"+" throws "+cType.toString()+")" + " ||\n" 
								         + "    execution("+this.typeDecl.getCClass().getJavaName()+"+.new(..)"+" throws "+cType.toString()+"))";
							}
							else{
								pc = "("+pc+ " ||" + "(execution(* "+this.typeDecl.getCClass().getJavaName()+"+.*(..)"+" throws "+cType.toString()+")" + " ||\n" 
								         + "    execution("+this.typeDecl.getCClass().getJavaName()+"+.new(..)"+" throws "+cType.toString()+")))";
							}
						}
					}
					code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac)");
					code.append(" throwing(JMLInternalRuntimeException rac$e)\n");
					code.append("    throws "+cType.toString()+" : "+pc);
					code.append(" && ");
					code.append("\n");
					code.append("   target(object$rac)");
					code.append(" {\n");	
					code.append("    Throwable cause = rac$e.getCause();\n");
					code.append("    if(cause instanceof "+cType.toString()+") {\n");
					code.append("      throw ("+cType.toString()+")cause;\n");
					code.append("    }\n");
					code.append("    JMLChecker.rethrowUncheckedException(cause);\n");
					code.append("  }");
					code.append("\n");
				}
			}
			
			if (Main.aRacOptions.multipleSpecCaseChecking()){
				if(Main.aRacOptions.clientAwareChecking()){
					code.append("\n");
					code.append("/** Generated by AspectJML to multiple spec case checking (CAC enabled) */\n");
					code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
					code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
					code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
					    append(adviceexecution).append(")");
					code.append(" && ");
					code.append("\n");
					code.append("   target(object$rac)");
					code.append(" && ");
					code.append("\n");
				    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
					code.append(" {\n");		
					code.append("   JMLChecker.hasAnyThrownInvariant();\n");
					code.append("   JMLChecker.hasAnyThrownConstraint();\n");
					code.append("   JMLChecker.hasAnyThrownNormalPostcondition();\n");
					code.append("   JMLChecker.hasAnyThrownExceptionalPostcondition();\n");
					if(Main.aRacOptions.crosscuttingContractSpecifications()){
						code.append(    "// Generated by AspectJML to enable modular signals_only checking (XCS enabled)/\n");
						code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
					}
					code.append("  }\n");	
				}
				else{
					if(Main.aRacOptions.callSiteInstrumentation()){
						code.append("\n");
						code.append("/** Generated by AspectJML to multiple spec case checking (Call Site enabled) */\n");
						code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
						code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
						    append(adviceexecution).append(")");
						code.append(" && ");
						code.append("\n");
						code.append("   target(object$rac)");
						code.append(" && ");
						code.append("\n");
					    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
						code.append(" {\n");		
						code.append("   JMLChecker.hasAnyThrownInvariant();\n");
						code.append("   JMLChecker.hasAnyThrownConstraint();\n");
						code.append("   JMLChecker.hasAnyThrownNormalPostcondition();\n");
						code.append("   JMLChecker.hasAnyThrownExceptionalPostcondition();\n");
						if(Main.aRacOptions.crosscuttingContractSpecifications()){
							code.append(    "// Generated by AspectJML to enable modular signals_only checking (XCS enabled)/\n");
							code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
						}
						code.append("  }\n");	
					}
                    if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
                    	code.append("\n");
    					code.append("/** Generated by AspectJML to multiple spec case checking (Execution Site enabled) */\n");
                    	code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
						code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
						      append(adviceexecution).append(")");
						code.append(" && ");
						code.append("\n");
						code.append("   this(object$rac)");
						code.append(" {\n");		
						code.append("   JMLChecker.hasAnyThrownInvariant();\n");
						code.append("   JMLChecker.hasAnyThrownConstraint();\n");
						code.append("   JMLChecker.hasAnyThrownNormalPostcondition();\n");
						code.append("   JMLChecker.hasAnyThrownExceptionalPostcondition();\n");
						if(Main.aRacOptions.crosscuttingContractSpecifications()){
							code.append(    "// Generated by AspectJML to enable modular signals_only checking (XCS enabled)/\n");
							code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
						}
						code.append("  }\n");	
					}
				}
			} 
			else {
				if(Main.aRacOptions.crosscuttingContractSpecifications()){
					if(Main.aRacOptions.clientAwareChecking()){
						code.append("\n");
						code.append("/** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */\n");
						code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
						code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
						    append(adviceexecution).append(")");
						code.append(" && ");
						code.append("\n");
						code.append("   target(object$rac)");
						code.append(" && ");
						code.append("\n");
					    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
						code.append(" {\n");		
						code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
						code.append("  }\n");	
					}
					else{
						if(Main.aRacOptions.callSiteInstrumentation()){
							code.append("\n");
							code.append("/** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */\n");
							code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
							code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
							code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
							    append(adviceexecution).append(")");
							code.append(" && ");
							code.append("\n");
							code.append("   target(object$rac)");
							code.append(" && ");
							code.append("\n");
						    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
							code.append(" {\n");		
							code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
							code.append("  }\n");	
						}
	                    if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
	                    	code.append("\n");
	                    	code.append("/** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */\n");
	                    	code.append("  after(final ").append(this.typeDecl.getCClass().getJavaName()).append(" object$rac): ");
							code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
							code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()+"+").append(".new(..))").
							      append(adviceexecution).append(")");
							code.append(" && ");
							code.append("\n");
							code.append("   this(object$rac)");
							code.append(" {\n");		
							code.append("   JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();\n");
							code.append("  }\n");	
						}
					}	
				}
			}
			
			if(Main.aRacOptions.clientAwareChecking()){
				code.append("\n");
				code.append("/** Generated by AspectJML to enhance error reporting (CAC enabled) */\n");
				code.append("  after() throwing (Throwable rac$e): ");
				code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
				code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
				     append(adviceexecution).append(")");
				code.append("{\n");
				code.append("    JMLChecker.hideAjmlSpecificStackTrace(rac$e);\n");
				code.append("  }\n");
			}
			else {
				if(Main.aRacOptions.callSiteInstrumentation()){
					code.append("\n");
					code.append("/** Generated by AspectJML to enhance error reporting (Call Site enabled) */\n");
					code.append("  after() throwing (Throwable rac$e): ");
					code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
					code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
					  append(adviceexecution).append(")");
					code.append("{\n");
					code.append("    JMLChecker.hideAjmlSpecificStackTrace(rac$e);\n");
					code.append("  }\n");
				}
				if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
					code.append("\n");
					code.append("/** Generated by AspectJML to enhance error reporting (Execution Site enabled) */\n");
					code.append("  after() throwing (Throwable rac$e): ");
					code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
					code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
					   append(adviceexecution).append(")");
					code.append("{\n");
					code.append("    JMLChecker.hideAjmlSpecificStackTrace(rac$e);\n");
					code.append("  }\n");
				}
			}
			typeDecl.addMember(RacParser.parseMethod(code.toString()));
			code = null;
		}
		
		
		// Adding utility Aspect code for multiple spec case checking, preconditions, Aspect stack tracing hiding - hemr
		if(AspectUtil.getInstance().isCompilationUnitRacable){
			StringBuffer code = new StringBuffer();
			if(!AspectUtil.getInstance().getPreconditionPointcut().equals("()")){
				code.append("\n");
				code.append("/** Generated by AspectJML to enhance precondition checking */\n");
				code.append("public static aspect UtilPreconditionChecking_"+typeDecl.ident()).append("{\n");
//				old code
//				if(!AspectUtil.getInstance().getPreconditionPointcut().equals("()")){
//					code.append("  before(): "+AspectUtil.getInstance().getPreconditionPointcut()).append("{\n");
//					code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
//					code.append("  }\n");
//				}
				if(Main.aRacOptions.clientAwareChecking()){
					code.append("  before(): ");
					code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
					code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
					append(adviceexecution).append(")");
					code.append("{\n");
					code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
					code.append("  }\n");
					if(AspectUtil.getInstance().getPreconditionPointcut().contains("execution")){
						code.append("  before(): ");
						code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
						append(adviceexecution).append(")");
						code.append("{\n");
						code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
						code.append("  }\n");
					}
				}
				else {
					if(Main.aRacOptions.callSiteInstrumentation()){
						code.append("  before(): ");
						code.append("(call( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || call(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
						append(adviceexecution).append(")");
						code.append("{\n");
						code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
						code.append("  }\n");
					}
					if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
						code.append("  before(): ");
						code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
						code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
						append(adviceexecution).append(")");
						code.append("{\n");
						code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
						code.append("  }\n");
					}
					else{
						if(AspectUtil.getInstance().getPreconditionPointcut().contains("execution")){
							code.append("  before(): ");
							code.append("(execution( * ").append(this.typeDecl.getCClass().getJavaName()+"+.*(..))").append("\n");
							code.append("          || execution(").append(this.typeDecl.getCClass().getJavaName()).append("+.new(..))").
							append(adviceexecution).append(")");
							code.append("{\n");
							code.append("    JMLChecker.hasAnyThrownPrecondition();\n");
							code.append("  }\n");
						}
					}
				}
				code.append("}\n");
				typeDecl.addMember(RacParser.parseMethod(code.toString()));
				code = null;
			}
		}
		
		// handling crossrefs for XCS specifications --- [[[hemr]]]
		if(Main.aRacOptions.crossrefs() != null){
			if(AspectUtil.getInstance().getCrossrefs().size() > 0){
				StringBuffer crossrefs = new StringBuffer("");
				String aspectName = this.typeDecl.getCClass().getJavaName().replace("$", ".").replace(".", "_")+"CrossRef";
				// header
				crossrefs.append("/* \n" +
						"* Copyright (C) 2013 Federal University of Pernambuco and\n" +
						"* University of Central Florida.\n" +
						"*\n"+
						"* This file is part of the AspectJML project\n"+
						"*\n"+
						"* Software distributed WITHOUT WARRANTY OF ANY KIND, either express or implied.\n " +
						"*\n" +
						"* NOTE that this .aj file is automatic generated for inputing in the common AspectJML tools.\n" +
						"* Contributor(s):\n" +
						"*/\n");
				crossrefs.append("public privileged aspect ").append(aspectName).append(" {\n");
				crossrefs.append("  static boolean advise = false;\n");
				for (Iterator iterator = AspectUtil.getInstance().getCrossrefs().iterator(); iterator.hasNext();) {
					String crossref = (String) iterator.next();
					crossrefs.append(crossref);
					crossrefs.append("\n");
				}
				crossrefs.append("}");
				
				// printing to the specified output directory --- [[[hemr]]]
				File dest = new File(Main.aRacOptions.crossrefs()+"\\"+aspectName+".aj");
				try {
					PrintWriter out = new PrintWriter(dest);
					out.write(crossrefs.toString());
					out.flush();
					out.close();
				} catch (FileNotFoundException e) {
//					e.printStackTrace();
					JmlRacGenerator.warn(this.typeDecl.getTokenReference(), 
							JmlMessages.MISSING_CROSSREF_DIR, aspectName+".aj"+" for type "+this.typeDecl.getCClass().getJavaName());
				}
			}
		}
		
		
		// reseting transtype issues for the next compilation unit
		AspectUtil.getInstance().emptyPreconditionNewMethodsAdvice();
		AspectUtil.getInstance().emptyPostconditionNewMethodsAfterAdvice();
		AspectUtil.getInstance().emptyPostconditionNewMethodsAroundAdvice();
		AspectUtil.getInstance().emptyExceptionsInSignalsClausesInCompilationUnit();
		AspectUtil.getInstance().resetCurrentCompilationUnitHasInvariants();
		AspectUtil.getInstance().resetCurrentCompilationUnitHasConstraints();
		AspectUtil.getInstance().emptyPreconditionPointcuts();
		AspectUtil.getInstance().emptyQuantifierUniqueID();
		AspectUtil.getInstance().emptyQuantifierInnerClasses();
		AspectUtil.getInstance().isCompilationUnitRacable = false;
		
		// reseting for XCS
		AspectUtil.getInstance().emptyPreconditionNewMethodsAdviceXCS();
		AspectUtil.getInstance().emptyPostconditionNewMethodsAfterAdviceXCS();
		AspectUtil.getInstance().emptyPostconditionNewMethodsAroundAdviceXCS();
		AspectUtil.getInstance().emptyCrossrefs();
		
		//finalizeTranslation();

	}

	// Rebelo - invariant translation based on AspectJ

	/**
	 * Translates invariants, for non-static invariants. This
	 * translating generates a AspectJ before advice responsible for checking
	 * the invariants before the methods execution. This method must be
	 * implemented by concrete subclasses.
	 * 
	 * @author Henrique Rebelo
	 */
	protected abstract void translateInvariantAsPrecondition();

	/**
	 * Translates invariants, both static and non-static invariants. This
	 * translating generates the two kinds of AspectJ advice responsible for
	 * checking the invariants after the methods execution. This method must be
	 * implemented by concrete subclasses.
	 * 
	 * @author Henrique Rebelo
	 */
	protected abstract void translateInvariantAsPostcondition();

	/** Translates history constraints, both static and non-static.
	 * This method must be implemented by concrete subclasses.
	 */
	protected abstract void translateConstraint();

//	private ArrayList laterMethods;

//	public String translateForSpecTestFile() {
//
//		String wrapperClass = null;
//
//		if (genSpecTestFile) {
//
//			JFieldDeclarationType[] fields = typeDecl.fields();
//
//			laterMethods = new ArrayList();
//			java.util.List list = new java.util.LinkedList();
//
//			// Add a field with identifier 'delegee' that will contain
//			// a reference to the class under test or to the Wrapper
//			// derived class of the class under test
//			if (!hasFlag(typeDecl.modifiers(),ACC_ABSTRACT))
//				list.add(new JFieldDeclaration(null,
//						new JVariableDefinition(null,ARacConstants.ACC_PUBLIC,
//								CTopLevel.getTypeRep(typeDecl.getCClass().
//										qualifiedName(),true),
//										"delegee",new JNameExpression(null,"null")),
//										null,null)
//				);
//
//			// Only model and ghost fields are put in the delegator
//			// class An access method is generated for protected
//			// fields
//			for (int i=0; i<fields.length; ++i) {
//				JFieldDeclarationType jp = fields[i];
//				if (hasFlag(jp.modifiers(),ACC_MODEL|ACC_GHOST)) {
//					list.add(jp);
//				}
//				else if (hasFlag(jp.modifiers(),ACC_PROTECTED)) {
//					String ss = 
//						"\npublic "  + jp.getType() + " prot$" + 
//						jp.ident() + "$" + typeDecl.ident() + "() {\n" 
//						+ "\t try { \n"
//						+ "\t\t java.lang.Class c = delegee().getClass();\n"
//						+ "\t\t java.lang.reflect.Method m " 
//						+ "= c.getMethod(\"spec$" + jp.ident()
//						+ "\",new Class[]{});\n"
//						+ "\t\t Object o = "
//						+ "m.invoke(delegee(),new Object[]{});\n"
//						+ "\t\t return " + unwrap(jp.getType(),"o") + ";\n"
//						+ "\t } catch(java.lang.Exception e) { \n"
//						+ "\t\t throw new java.lang.RuntimeException("
//						+ "e.toString()); /* FIXME */\n" 
//						+ "\t }\n"
//						+ "}\n" ;
//					laterMethods.add(ss);
//				}
//			}
//
//			// Adjust the set of methods - only public and model
//			// methods can be called
//			ArrayList originalMethods = typeDecl.methods();
//			ArrayList v = new ArrayList();
//			boolean isObjectType = 
//				typeDecl.getCClass().getType().equals(CStdType.Object);
//			for (Iterator ii = originalMethods.iterator(); ii.hasNext(); ) {
//				JMethodDeclarationType jm = 
//					(JMethodDeclarationType)(ii.next());
//				if (isObjectType && hasFlag(jm.modifiers(),ACC_FINAL)) {
//					continue;
//				}
//				if (hasFlag(jm.modifiers(), ACC_PUBLIC|ACC_MODEL)) {
//					v.add(jm);
//				}
//			}
//
//			typeDecl.setMethods(v);
//
//			// Generate Wrapper class
//
//			if (genWrapperClass) {
//
//				// add the wrapper nested class that is a derived from
//				// the class under test; this provides access to
//				// protected members and enables wrapping the
//				// constructors
//
//				StringBuffer b = new StringBuffer(1000);
//				b.append("\npublic static class Wrapper extends " +
//						typeDecl.getCClass().qualifiedName().replace('/','.') 
//						+ " {\n");
//
//
//				// Add versions of all constructors and protected
//				// methods of the class under test
//				for (Iterator ii = originalMethods.iterator(); ii.hasNext(); ) {
//					Object o = ii.next();
//					JMethodDeclarationType jm = (JMethodDeclarationType)o;
//					if (hasFlag(jm.modifiers(),ACC_MODEL) || 
//							hasFlag(jm.modifiers(),ACC_GHOST)) continue;
//					if (!hasFlag(jm.modifiers(),ACC_PROTECTED) && !hasFlag(jm.modifiers(),ACC_PUBLIC)) continue;
//					if (o instanceof JConstructorDeclarationType) {
//						JConstructorDeclarationType jc = (JConstructorDeclarationType)o;
//						JFormalParameter[] params = jc.parameters();
//						StringBuffer ptlist = new StringBuffer();
//						StringBuffer plist = new StringBuffer();
//						for (int i = 0; i<params.length; ++i) {
//							if (i != 0) { plist.append(", "); ptlist.append(", "); }
//							plist.append(params[i].ident());
//							ptlist.append(params[i].toString());
//						}
//						b.append(
//								"  public Wrapper("+ptlist+") { super("+plist+"); }\n");
//
//						b.append("\n");
//					} else {
//						JFormalParameter[] params = jm.parameters();
//						StringBuffer cparams = new StringBuffer();
//						StringBuffer oparams = new StringBuffer();
//						StringBuffer ptlist = new StringBuffer();
//						StringBuffer plist = new StringBuffer();
//						for (int i = 0; i<params.length; ++i) {
//							if (i != 0) { plist.append(", "); ptlist.append(", "); cparams.append(","); oparams.append(",");}
//							plist.append(params[i].ident());
//							ptlist.append(params[i].toString());
//							cparams.append(params[i].getType().toString() + ".class");
//							oparams.append(wrap(params[i].getType(),params[i].ident()));
//						}
//						StringBuffer elist = new StringBuffer();
//						CClassType[] ex = jm.getExceptions();
//						for (int i = 0; i<ex.length; ++i) {
//							if (i != 0) { elist.append(", ");}
//							elist.append("throws ");
//							elist.append(ex[i].qualifiedName().replace('/','.'));
//						}
//
//						b.append(
//								"  public " + jm.returnType() + " " + jm.ident() + "("+ptlist+") " 
//								+ elist.toString() 
//								+ " { " + (jm.returnType().isVoid()?"":"return ")
//								+ "super." + jm.ident() + "("+plist+"); }\n");
//
//						String ss = 
//							"  public "  + jm.returnType() + " prot$" + jm.ident() + "("+ptlist+") " 
//							+ elist.toString() 
//							+ " { \n\ttry { \n\t\t" + (jm.returnType().isVoid()?"":"return ")
//							+ unwrap(jm.returnType(),
//									"delegee().getClass().\n\t\t\tgetMethod(\""+jm.ident()+"\",new Class[]{"+cparams+"}).\n\t\t\tinvoke(delegee(),new Object[]{"+oparams+"})") + ";\n" +
//									"\t} catch (java.lang.Exception e) {\n" +
//									"\t\tthrow new java.lang.RuntimeException(e.toString()); \n" +
//									"\t}\n" +
//									"}\n" ;
//						laterMethods.add(ss);
//
//						b.append("\n");
//					}
//
//				}
//
//
//				CClass cc = typeDecl.getCClass();
//
//				// Add accessors for all the fields (particularly necessary for protected fields)
//				do {
//
//					for (Iterator ii = cc.fields().iterator(); ii.hasNext(); ) {
//						CField field = (CField)(ii.next());
//						long m = field.modifiers();
//						if (!hasFlag(m,ACC_MODEL) && !hasFlag(m,ACC_GHOST) &&
//								(hasFlag(m,ACC_PUBLIC) || hasFlag(m,ACC_PROTECTED))) {
//							b.append(
//									"  public " + field.getType() + " spec$" + 
//									field.ident() + "() {\n" +
//									"    return " + field.ident() + ";\n" +
//									"  }\n"
//							);
//						}
//					}
//
//					cc = cc.getSuperClass();
//
//				} while (cc != null);
//
//				b.append("}\n");
//
//				wrapperClass = b.toString();		
//
//
//			}
//
//			// Reset the list of fields - these are the ones that will be included in the test framework class.
//			typeDecl.setFields((JPhylum[])list.toArray(new JPhylum[0]));
//
//
//		}
//		return wrapperClass;
//	}

//	private String wrap(CType t, String val) {
//		if (!t.isPrimitive()) return val;
//		if (t.equals(CStdType.Integer))   return "new java.lang.Integer("+val+")";
//		if (t.equals(CStdType.Boolean))   return "new java.lang.Boolean("+val+")";
//		if (t.equals(CStdType.Short))     return "new java.lang.Short("+val+")";
//		if (t.equals(CStdType.Float))     return "new java.lang.Float("+val+")";
//		if (t.equals(CStdType.Double))    return "new java.lang.Double("+val+")";
//		if (t.equals(CStdType.Char))      return "new java.lang.Character("+val+")";
//		if (t.equals(CStdType.Byte))      return "new java.lang.Byte("+val+")";
//		if (t.equals(CStdType.Long))      return "new java.lang.Long("+val+")";
//		return val;
//	}

//	private String unwrap(CType t, String val) {
//		if (t.isVoid()) return val;
//		if (!t.isPrimitive()) return "("+t.toString()+")" +val;
//		if (t.equals(CStdType.Integer))   return "((java.lang.Integer)"+val+").intValue()";
//		if (t.equals(CStdType.Boolean))   return "((java.lang.Boolean)"+val+").booleanValue()";
//		if (t.equals(CStdType.Short))     return "((java.lang.Short)"+val+").shortValue()";
//		if (t.equals(CStdType.Float))     return "((java.lang.Float)"+val+").floatValue()";
//		if (t.equals(CStdType.Double))    return "((java.lang.Double)"+val+").doubleValue()";
//		if (t.equals(CStdType.Char))      return "((java.lang.Character)"+val+").charValue()";
//		if (t.equals(CStdType.Byte))      return "((java.lang.Byte)"+val+").byteValue()";
//		if (t.equals(CStdType.Long))      return "((java.lang.Long)"+val+").longValue()";
//		return val;
//	}
//
//	public void postTranslationChangesForSpecTestFile(String wrapperClass) {
//		if (!genSpecTestFile) return;
//
//		// Here we do any changes in support of specification test files 
//		// that we do not want altered by the normal translation phases.
//
//		// Add a method that returns the delegee
//
//		if (hasFlag(typeDecl.modifiers(),ACC_ABSTRACT)) {
//			typeDecl.addMember(RacParser.parseMethod("\nabstract public java.lang.Object" 
//					+ " delegee();\n"));
//		} else if (genWrapperClass) {
//			typeDecl.addMember(RacParser.parseMethod("\npublic java.lang.Object" 
//					+ " delegee() { return delegee; }\n"));
//		} else {
//			typeDecl.addMember(RacParser.parseMethod("\npublic java.lang.Object" 
//					+ " delegee() { return delegee; }\n"));
//		}
//		typeDecl.addMember(RacParser.parseMethod("\npublic " 
//				+ typeDecl.getCClass().qualifiedName().replace('/','.')
//				+ " delegee_" + typeDecl.ident() + "() { return (" 
//				+ typeDecl.getCClass().qualifiedName().replace('/','.')
//				+ ")delegee(); }\n"));
//
//		// Add an accessor for every protected method
//
//		for (Iterator iii = laterMethods.iterator(); iii.hasNext(); ) {
//			String s = (String)(iii.next());
//			typeDecl.addMember(RacParser.parseMethod(s));
//		}
//
//
//		if (genWrapperClass) {
//
//			// Parses Wrapper class and adds it as a nested class to
//			// typeDecl, despite the fact that the method is parseMethod
//			// and it returns a RacMethodDeclaration (both should refer to
//			// members).  
//			typeDecl.addMember(RacParser.parseMethod(wrapperClass));
//		}
//
//		if (!genWrapperClass && !hasFlag(typeDecl.modifiers(),ACC_ABSTRACT)) {
//			// Add a method to create a testspecs.p.C instance 
//			// from a p.C instance
//
//			typeDecl.addMember(RacParser.parseMethod(
//					"\n\npublic " + typeDecl.ident() + "(" + typeDecl.getCClass().qualifiedName().replace('/','.')
//					+ " obj) { delegee = obj; }\n")
//			);
//
//			typeDecl.addMember(RacParser.parseMethod(
//					"\n\npublic static " + typeDecl.ident() + " make(" + typeDecl.getCClass().qualifiedName().replace('/','.')
//					+ " obj) { return new " + typeDecl.ident() + "(obj); }\n")
//			);
//		}
//	}
	
	private String privacy(long modifiers) {
		if (hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_PUBLIC))
			return "public ";
		else if (hasFlag(modifiers, ACC_SPEC_PROTECTED | ACC_PROTECTED))
			return "protected ";
		else if (hasFlag(modifiers, ACC_PRIVATE))
			return "private ";
		else
			return ""; // package
	}
	
	
	protected void translateModelFields(Collection fields) {
		for (Iterator iterator = fields.iterator(); iterator.hasNext();) {
			CField field = (CField)(iterator.next());
		    long m = field.modifiers();
		    String mod = field.isStatic() ? "static " : "";
		    String modHeader = field.isStatic() ? "static" : "instance";
		    CType typeField = field.getType();
		    String strFieldType = toString(typeField);
		    String nameAjmlc = field.owner().qualifiedName().replace('/', '.').replace("$", ".") + '.' + field.ident();
		    if (hasFlag(m,ACC_MODEL)){
		    	String repMethodAjmlc = "";
//		    	if(field.owner().isInterface() && field.isStatic()){
//		    		repMethodAjmlc = this.privacy(field.modifiers()) + mod + strFieldType + " " + field.ident() +";\n";
//		    		AspectUtil.getInstance().appendInterfaceStaticModelFields(repMethodAjmlc);
//		    	}
//		    	else{
//		    		repMethodAjmlc = (
//							"\n/** Generated by JML to implement the "+ modHeader +" model field " + 
//							field.ident() + ". */\n" +
//							"private " + mod + strFieldType + " " + nameAjmlc +";\n");
//			    	typeDecl.addMember(RacParser.parseMethod(repMethodAjmlc));
//		    	}
		    	repMethodAjmlc = (
						"\n/** Generated by AspectJML to implement the "+ modHeader +" model field " + 
						field.ident() + ". */\n" +
						"private " + mod + strFieldType + " " + nameAjmlc +";\n");
		    	typeDecl.addMember(RacParser.parseMethod(repMethodAjmlc));
		    	AspectUtil.getInstance().isCompilationUnitRacable = true;
		    }
		}
	}

	/** 
	 * Translates <code>represents</code> clauses of this type declaration. 
	 * For each executable (i.e., functinal abstraction) form of 
	 * <code>represents</code> clause, this method generates a 
	 * <em>model field accessor method</em> that calculates the value 
	 * of the model field in terms of the <code>represents clause</code>'s
	 * expression. The accessor method has the following general form:
	 * 
	 * <pre>
	 * [[represents m <- E;]] ==
	 *   protected T m() {
	 *     T v = T_init;
	 *     [[E, v]]
	 *     return v;
	 *   }
	 * </pre>
	 * where <code>T</code> is the type of expression <code>E</code>
	 * and <code>v</code> is a unique local variable.
	 * The generated method declaration is added to the current type
	 * (or surrogate class if the type is an interface), and the field
	 * is marked that its model access method is generated.
	 * 
	 * <pre><jml>
	 * requires repDecls != null;
	 * </jml></pre>
	 *
	 * @see #translateField(JmlFieldDeclaration)
	 * @see #addNewMethod(JmlMethodDeclaration)
	 * @see #setAccessorGenerated(CField)
	 */
	protected void translateRepresents(JmlRepresentsDecl[] repDecls) {
		for (int i = 0; i < repDecls.length; i++) {
			JmlSourceField field = repDecls[i].getField();

			if (isRepresentsDeclExecutable(repDecls[i]) 
					&& !isAccessorGenerated(field)
			) {
				// add a corresponding model accessor method.
				JmlSpecExpression expr =  repDecls[i].specExpression();	    
				typeDecl.addMember(modelFieldAccessor(field, expr));
				setAccessorGenerated(field);
				AspectUtil.getInstance().isCompilationUnitRacable = true;
			}
		}
	}
	
	private void markHelperMethods(ArrayList methods){
		StringBuffer code = new StringBuffer("");
		
		for (Iterator i = methods.iterator(); i.hasNext(); ) {
			JmlMethodDeclaration jmd = (JmlMethodDeclaration)i.next();
			if(jmd.isHelper()){
				String methodQualifiedName = null;
				if (jmd.isConstructor()){
					methodQualifiedName = jmd.getMethod().getJavaName().replaceFirst(".<init>", ".new");
				}
				else{
					methodQualifiedName = jmd.getMethod().getJavaName();	
				}
				code.append("\n");
				code.append("declare ").append((jmd.isConstructor()?"@constructor:":"@method: "+jmd.returnType().toString())).append(" ").append(methodQualifiedName)
				.append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(jmd.parameters()).toString()).append("): ").append("@JMLHelper;");
			}
		}
		
		if(!code.toString().equals("")){
			if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4){
				String javadoc = "/** Generated by AspectJML to mark the helper methods of type "+this.typeDecl.ident()+". */";
				typeDecl.addMember(RacParser.parseMethod(javadoc));
				code.append("\n");
				typeDecl.addMember(RacParser.parseMethod(code.toString()));
			}
		}
	}
	
	/**
	 * Translates a class body, either of class or interface.
	 *
	 * @param inners inner classes
	 * @param methods mthod declarations
	 * @param fieldsAndInits field declarations
	 *
	 * <pre><jml>
	 * requires inners != null && methods != null && fieldsAndInits != null;
	 * </jml></pre>     
	 */
	protected void translateBody(ArrayList inners, ArrayList methods, 
			JPhylum[] fieldsAndInits ) 
	{
		// !FIXME! translate inner classes (i.e., inners)

		// translate methods
		for (Iterator i = methods.iterator(); i.hasNext(); ) {
			translateMethod((JmlMethodDeclaration)i.next());
		}
		// translate fields
		for (int i = 0; i < fieldsAndInits.length ; i++) {
			if (fieldsAndInits[i] instanceof JmlFieldDeclaration) {
				fieldsAndInits[i] = 
					translateField((JmlFieldDeclaration)fieldsAndInits[i]);
			}
		}
		// translate inner fields - [[[hemr]]]
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				fieldsAndInits = currentInnerType.fieldsAndInits();
				for (int i = 0; i < fieldsAndInits.length ; i++) {
					if (fieldsAndInits[i] instanceof JmlFieldDeclaration) {
						fieldsAndInits[i] = 
							translateField((JmlFieldDeclaration)fieldsAndInits[i]);
					}
				}
			}
		}
	}

	/**
	 * Translates a JML field declaration,
	 * <code>fieldDecl</code>. This method strips off the final
	 * modifier from the field declaration.  If necessary, this method
	 * should be overwritten by subclasses to specially handle final,
	 * model, model, spec_public, and spec_protected fields.
	 *
	 * <pre><jml>
	 * requires fieldDecl != null;
	 * modifies fieldDecl.*;
	 * ensures \result != null && \result == fieldDecl;
	 * </jml></pre>
	 */
	protected JmlFieldDeclaration translateField(
			JmlFieldDeclaration fieldDecl) 
	{
		// A blank final instance field may become
		// definitely-not-assigned after RAC translation because the
		// constructor body is wrapped with a try-catch statement. As
		// a fix, we turn such a final field into a non-final.
		long modifiers = fieldDecl.modifiers();
		if (!fieldDecl.hasInitializer() 
				&& !hasFlag(modifiers, ACC_STATIC) 
				&& hasFlag(modifiers, ACC_FINAL)) {
			fieldDecl.setModifiers(modifiers & (0xffffffffffffffffL ^ ACC_FINAL));
		}
		return fieldDecl;
	}

	/**
	 * Translates the given model method (or constructor),
	 * <code>mdecl</code>. !FIXME!describe translation rules.
	 */
	protected void translateModelMethod(JmlMethodDeclaration mdecl) {
		//@ assume mdecl.isModel();

		// if not executable, we are done.
		if (!mdecl.isExecutableModel()) {
			return;
		}

		// turn it into a Java method or consturctor. Perhaps,
		// generate new one instead of mutating it?
		mdecl.setModifiers(mdecl.modifiers() & (~ACC_MODEL));

		// for a constructor, we are almost done
		if (mdecl.isConstructor()) {
			// if protected or package-visivible, make it public so
			// that dynamic call can be maded to it by subclasses or
			// other classes in the same package.
			if (!(mdecl.isPublic() || mdecl.isPrivate())) { 
				long mod = mdecl.modifiers();
				mod = (mod | ACC_PUBLIC) & (~ACC_PROTECTED) & (~ACC_PRIVATE);
				mdecl.setModifiers(mod);
			}
			return;
		}

		// for a public or private method, we are done.
		if (mdecl.isPublic() || mdecl.isPrivate()) {
//			return;
		}

		// for a protected and package-visible method, build an access
		// method so that subclasses or other classes in the same
		// package can call it dynamically.
		long mod = mdecl.modifiers();
		mod = (mod | ACC_PUBLIC) & (~ACC_PROTECTED) & (~ACC_PRIVATE);
		JMethodDeclaration decl = new JMethodDeclaration(
				mdecl.getTokenReference(),
				mod,
				CTypeVariable.EMPTY,
				mdecl.returnType(),
				TransUtils.modelPublicAccessorName(mdecl.getMethod()),
				mdecl.parameters(), 
				mdecl.getExceptions(),
				mdecl.body(), 
				null,
				null);

		// finally, add the accessor to the host class
		addNewMethod(RacParser.parseMethod(
				"\n/** Generated by AspectJML to access the model method " +
				mdecl.ident() + ". */$0", decl));
	}

	/**
	 * Translates a JML method declaration. A translation of JML method
	 * declaration produces four new methods, and the original method
	 * is renamed and made <tt>private</tt>-accessible:
	 * 
	 * <p>
	 * <ul><li>
	 * <em>Precondition checking method</em>. A <tt>protected</tt> method
	 * to check the precondition of the original method (refer to the class
	 * <code>PreconditionMethod</code>).
	 * </li></ul>
	 *
	 * <ul><li>
	 * <em>Normal and exceptional postcondition checking methods</em>. 
	 * A couple of <tt>protected</tt> methods to check the normal and
	 * exceptional postconditions of the original method
	 * (refer to the classes <code>PostconditionMethod</code> and
	 * <code>ExceptionalPostconditionMethod</code>).
	 * </li></ul>
	 *
	 * <ul><li>
	 * <em>Wrapper method</em>. A wrapper method that wraps the original
	 * method with pre and postcondition checking (refer to the class
	 * <code>WappersMethod</code>).
	 *
	 * <p>
	 * The translation also generate several new instance fields to store
	 * temporally values used by the assertion checking methods. 
	 * There are three kinds of variables that are generated and declared
	 * as instance fields.
	 * 
	 * <p>
	 * <ul><li>
	 * <em>Precondition variables</em>.
	 * </li></ul>
	 *
	 * <ul><li>
	 * <em>Old (\old) expression variables</em>.
	 * </li></ul>
	 *
	 * <ul><li>
	 * <em>Specification variables</em>.
	 * </ul></li>
	 *
	 * <p>
	 * Similarly, translation of JML constructor declaration also produces 
	 * four new methods, and the original constructor becomes a wrapper
	 * method (refer to the class <code>TransConstructor</code>).
	 *
	 * <pre><jml>
	 * requires mdecl != null;
	 * </jml></pre>
	 */
	protected abstract void translateMethod(JmlMethodDeclaration mdecl);

	/** 
	 * Returns a pair of ghost field accessor methods (getter and
	 * setter) for the given ghost field declaration. The name of both
	 * accessors is <code>MN_GHOST + ident + "$" + className</code>,
	 * where the constant MN_GHOST is usually <code>"ghost$"</code>
	 * and <code>ident</code> is the name of the ghost field. The
	 * accessor methods has the following general structure:
	 *
	 * <pre>
	 *  public [static] T ghost$v$C() {
	 *     return v;
	 *  } 
	 *  public [static] void ghost$v$C(T x) {
	 *     v = x;
	 *  } 
	 * </pre>
	 *
	 * This method also generates a private field for storing ghost
	 * values and possibly an initializer block too. They are stored
	 * in the given field declaration for later pretty-printing (see
	 * RacPrettyPrinter.visitJmlFieldDeclaration).
	 * 
	 * <pre>
	 *  private [static] T v;
	 *  [static] {
	 *     v = initializer;
	 *  }
	 * </pre>
	 *
	 * <pre><jml>
	 * requires fdecl != null && hasFlag(fdecl.modifiers(), ACC_GHOST);
	 * modifies fdecl.*;
	 * ensures \result != null;
	 * </jml></pre>
	 */
//	protected JmlMethodDeclaration ghostFieldAccessors(
//			JmlFieldDeclaration fdecl) {
//		// initialize local variables
//		final CField field = fdecl.getField();
//		final String mod = field.isStatic() ? "static " : "";
//		final CType type = field.getType();
//		final String ident = field.ident();
//
//		// translate the initializer if exists
//		RacNode init = null;
//		if (fdecl.hasInitializer()) {
//			VarGenerator gen = VarGenerator.forMethod(varGen);
//			RacContext ctx = RacContext.createNeutral();
//			JExpression expr = fdecl.variable().expr();
//			String val = defaultValue(type);
//			String v1 = gen.freshVar();
//			TransExpression trans = new TransExpression(gen,ctx,expr,v1,typeDecl);
//			init = trans.stmt().incrIndent();
//
//			// translated initializer: { T v; [[expr, v]]; g = v; }
//			init = RacParser.parseStatement(
//					"\n/** Generated by JML to initialize ghost variable " +
//					ident + ". */\n" +
//					mod + "{\n" + 
//					"  " + toString(type) + " " + v1 + " = " + val + ";\n" +
//					"$0\n" +
//					"  " + ident + " = " + v1 + ";\n" +
//					"}",
//					init);
//		}
//
//		// generate a new private field (and possibly an initializer
//		// block too) for the ghost variable, and store it to the
//		// field declaration. Why store it in the field declaration?
//		// Because we want to pretty-print it in the originally
//		// declared order (see RacPrettyPrinter.visitJmlFieldDeclaration).
//		// E.g., x in the ghost variable initializer should denote 100.
//		// int x = 100;
//		// //@ ghost v = x + 100;
//		fdecl.setAssertionCode(RacParser.parseStatement(
//				"\n/** Generated by JML for ghost variable " + 
//				field.ident() + ". */\n" +
//				"private " +mod+ "transient " +toString(type)+ " " +ident+ ";\n" +
//				(init == null? "" : "$0\n"),
//				init));
//
//		// name of getter/setter method: ghost$varName$typeName.
//		String mn = MN_GHOST + ident + "$" + field.owner().ident();
//
//		// generate and return a pair of access methods
//		return RacParser.parseMethod(
//				"\n/** Generated by JML to access ghost variable " + 
//				field.ident() + ". */\n" +
//				"public " + mod + toString(type) + " " + mn + "() {\n" +
//				"  return " + ident + ";\n" +
//				"}\n" +
//
//				"\n/** Generated by JML to set ghost variable " + 
//				field.ident() + ". */\n" +
//				"public " +mod+ "void " +mn+ "(" +toString(type)+ " rac$x) {\n"+
//				"  " +ident+ " = rac$x;\n" +
//		"}\n");
//	}

	/**
	 * Returns declarations of class/instance initialization
	 * flags. The initialization flags indicate if classes/instances
	 * have finished their initializations, and are used to prevent
	 * invariant checks from happening during initialization.
	 */
//	protected JmlMethodDeclaration initFlags() {
//		return RacParser.parseMethod(
//				"\n/** Generated by JML to indicate if the class has completed\n" +
//				"   * its initialization. */\n" +
//				"private static transient boolean " + VN_CLASS_INIT + 
//				" = true;\n\n"+
//
//				"/** Generated by JML to indicate if an instance has completed\n" +
//				"  * its initialization. */\n" +
//				"private transient boolean " +VN_INIT+ " = true;\n");
//	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/** Adds a new method declaration, <code>mdecl</code>, to the 
	 * instrumented type.
	 */
	protected abstract void addNewMethod(JmlMethodDeclaration mdecl);

	/**
	 * Returns a model accessor method for a model field with 
	 * the given expression (of the <code>represents</code> clause).
	 *
	 * @param field model field
	 * @param expr the right hand side of the <code>represents</code>
	 *             clause (e.g., <code>E</code> in <code>m &lt;- E</code>.
	 *
	 * <pre><jml>
	 * requires field != null && field.isModel() && expr != null;
	 * ensures \result != null;
	 * </jml></pre>
	 */
	private JmlMethodDeclaration modelFieldAccessor(JmlSourceField field,
			JExpression expr) {
		CType typeExp = expr.getApparentType();
		CType typeField = field.getType();
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		String var = mvarGen.freshVar();
		String val = defaultValue(typeField);
		RacContext ctx = RacContext.createNeutral();
		JExpression expFinal;
		if(typeExp != typeField) {
			expFinal = new JUnaryPromote(expr, typeField);	    
		} else {//here don't need to care about overflow for the typecheck will deal with it.
			expFinal = expr;
		}
		TransExpression trans 
		= new TransExpression(mvarGen,ctx,expFinal,var,typeDecl);
		TransExpression2 transAjmlc = new TransExpression2(mvarGen, ctx, expFinal, var, typeDecl, "JMLEntryPreconditionError");
		RacNode stmt = trans.stmt().incrIndent();
		String mod = field.isStatic() ? "static " : "";
		String name = MN_MODEL + field.ident() + "$" + field.owner().ident();
		String nameAjmlc = field.owner().qualifiedName().replace('/', '.') + '.' + field.ident();
		String context = field.isStatic() ? "" : field.owner().qualifiedName().replace('/', '.').replace("$", ".")+ " object$rac";
		String hasTarget = field.isStatic() ? "" : " && target (object$rac)";
		String modelFieldUpdate = field.isStatic() ? nameAjmlc : "object$rac." + field.ident();
		
		String strFieldType = toString(typeField);
//		String repMethod = (
//				"\n/** Generated by AspectJML to access the model field " + 
//				field.ident() + ". */\n" +
//				"public " + mod + strFieldType + " " + name + "() {\n" +
//				"  " + strFieldType + " " + var + " = " + val + ";\n" +
//				"$0\n" +
//				"  return " + var + ";\n" +
//		"}\n");
		String representsExpUtil = "((" + typeDecl.getCClass().qualifiedName().replace('/', '.').replace("$", ".") + ")object$rac).";
		String representsExpStr = AspectUtil.changeThisOrSuperRefToAdviceRef(transAjmlc.stmtAsString(), typeDecl).replace("object$rac.", representsExpUtil);
		String instanceOf = field.isStatic() ? "" : "\n&& if (object$rac instanceof "+typeDecl.getCClass().qualifiedName().replace('/', '.').replace("$", ".") + ")";
		if(typeDecl.getCClass().qualifiedName().equals(field.owner().qualifiedName())){
			instanceOf = "";
		}
		String repMethodAjmlc = (
				"\n/** Generated by AspectJML to access the model field " + 
				field.ident() + ". */\n" +
				"before (" + context + "): get(" + strFieldType + " " + nameAjmlc + ")" + hasTarget + instanceOf +"{\n" +
				"  try {\n"+
				"   "+ modelFieldUpdate + " = " + representsExpStr + ";\n" +
				"  } catch (Throwable rac$cause) {\n  "+
				"     if(rac$cause instanceof JMLAssertionError) {\n" +
				"      throw (JMLAssertionError) rac$cause;\n"+
				"     }\n"+
				"     else {\n"+
				"      throw new JMLEvaluationError(\"\" + rac$cause);\n" +
				"     }\n"+
				"  }\n"+
				"}\n");
		return RacParser.parseMethod(repMethodAjmlc, stmt);
	}

	/**
	 * Finds the applicable <code>represents</code>clause for a given
	 * model field by searching through the superclass and interface
	 * hierachies starting from the given type declaration.  If such a
	 * clause is found, returns the type declaration that includes the
	 * clause; otherwise, returns <code>null</code>.
	 *
	 * <pre><jml>
	 * requires tdecl != null && 
	 *   field != null && hasFlag(field.modifiers(),ACC_MODEL);
	 * ensures \result != null ==> (* \result has represents clause  r 
	 *   such that !r.isRedundantly() && r.usesAbstractionFunction() && 
	 *   r.storeRef() refers to field *);
	 * </jml></pre>
	 */
//	protected JmlTypeDeclaration findTypeWithRepresentsFor(
//			JmlTypeDeclaration tdecl, CField field) 
//	{
//		JmlTypeDeclaration repDecl 
//		= tdecl.findTypeWithRepresentsFor(field);
//		if (repDecl != null) {
//			JmlRepresentsDecl[] rdecls = repDecl.representsDecls();
//			for (int i = 0; i < rdecls.length; i++) {
//				try { 
//					if ( isRepresentsDeclExecutable(rdecls[i]) 
//							&& field == rdecls[i].getField()) {
//						return repDecl;
//					}
//				} catch (NullPointerException e) {
//					// If tdecl is not type checked (e.g., recursively
//					// included type), the getField method call throws
//					// a NullPointerException.
//					if (field.ident().equals(rdecls[i].ident())) {
//						JmlRacGenerator.fail(rdecls[i].getTokenReference(),
//								RacMessages.RECURSIVELY_REFERENCED_TYPE,
//								field.ident(), tdecl.ident());
//					}
//				}
//			}
//		}
//
//		return null; // no such type declaration found
//	}

	/** 
	 * Returns <code>true</code> if the given <code>represents</code> 
	 * declaration is translatable. A <code>represents</code> declaration is 
	 * <em>translatable</em> if the following conditions are satisfied:
	 * <p>
	 * <ul>
	 * <li> It is not redundant.
	 * <li> It uses a functional abstraction; i.e., it is of the form: 
	 *      <code>x &lt;- E</code>).
	 * </ul>
	 * </p>
	 * <pre><jml>
	 * requires rdecl != null;
	 * </jml></pre>
	 */
	private static boolean isRepresentsDeclExecutable(
			JmlRepresentsDecl rdecl){
		return !rdecl.isRedundantly() && !rdecl.usesAbstractionRelation();
	}

	/** 
	 * Returns a method declaration that makes a dynamic call to the
	 * given method using the Java's reflection facility. The target
	 * method is specified by its name, its owner's class name,
	 * formal parameter types, and actual arguments. The target method
	 * is typically an access method generated by the runtime
	 * assertion checker, such as an accessor for a model, ghost,
	 * spec_public, or spec_protected field, a setter for a ghost
	 * field, and an accessor for a spec_public or spec_protected
	 * method. The return value is that of the target method, if
	 * necessary, wrapped in an object. If the target method is not
	 * found, a instance of JMLNonExecutableException is thrown. If
	 * the target method throws a RuntimeException, including
	 * JMLNonExecutableException, the exception is rethrown; for other
	 * types of exceptions, an instanceof RuntimeException is thrown.
	 *
	 * <pre><jml>
	 * ensures \result != null;
	 * </jml></pre>
	 */
//	protected JmlMethodDeclaration dynamicInvocationMethod() {
//		return RacParser.parseMethod(
//				"\n/** Generated by JML to make dynamic calls to spec_public,\n" +
//				" * spec_protected, or model methods or constructors. */\n" +
//				"private static java.lang.Object rac$invoke(java.lang.String clsName, java.lang.Object self,\n" +
//				"  java.lang.String name, java.lang.Class types[], java.lang.Object args[]) {\n" +
//				"  try {\n" +
//				"    java.lang.Class clazz = rac$forName(clsName);\n" +
//				"    java.lang.Object inst = self;\n" +
//				"    //if (self != null\n" +
//				"    //   && !(self instanceof JMLSurrogate)) {\n" +
//				"      inst = " +receiver("clsName", "clazz", "self")+ ";\n" +
//				"    //}\n" +
//				"    if (name == null) {\n" +
//				"      return clazz.getConstructor(types).newInstance(args);\n" +
//				"    } else {\n" +
//				"      java.lang.reflect.Method meth =\n" +
//				"        " +TN_JMLSURROGATE+ ".getMethod(clazz, name, types);\n" +
//				"      return meth.invoke(inst, args);\n" +
//				"    }\n" +
//				"  }\n" +
//				"  catch (java.lang.reflect.InvocationTargetException e) {\n" +
//				"    // exception thrown by the invoked method\n"+
//				"    java.lang.Throwable thr = e.getTargetException();\n" +
//				"    if (thr instanceof java.lang.RuntimeException) {\n" +
//				"      throw (java.lang.RuntimeException) thr;\n" +
//				"    }\n" +
//				"    throw new java.lang.RuntimeException(e.getMessage());\n" +
//				"  }\n" +
//				"  catch (java.lang.Throwable e) {\n" +
//				"     //System.out.println(name + e.getClass().getName());\n" +
//				"     //e.printStackTrace();\n" +
//				"     throw JMLChecker.ANGELIC_EXCEPTION;\n" +
//				"  }\n" +
//		"}\n");
//	}

	/** 
	 * Returns a method declaration that returns the class object
	 * associated with the class or interface with the given
	 * string name.
	 *
	 * <pre><jml>
	 * ensures \result != null;
	 * </jml></pre>
	 */
//	protected JmlMethodDeclaration forNameMethod() {
//		return RacParser.parseMethod(
//				"\n/** Generated by JML to return the Class object associated\n" +
//				" * with the class or interface with the given string name. */\n" +
//				"private static java.lang.Class rac$forName(java.lang.String className) {\n"+
//				"  java.lang.Object clazz = JMLChecker.classes.get(className);\n" +
//				"  if (clazz == JMLChecker.NO_CLASS) {\n" +
//				"    throw new java.lang.RuntimeException(className);\n" +
//				"  } else if (clazz != null) {\n" +
//				"    return (java.lang.Class) clazz;\n" +
//				"  }\n" +
//				"  try {\n" +
//				"    clazz = java.lang.Class.forName(className);\n" +
//				"    JMLChecker.classes.put(className, clazz);\n" +
//				"    return (java.lang.Class) clazz;\n" +
//				"  } catch (java.lang.ClassNotFoundException e) {\n" +
//				"    JMLChecker.classes.put(className, JMLChecker.NO_CLASS);\n" +
//				"    throw new java.lang.RuntimeException(className);\n" +
//				"  }\n" +
//		"}\n");
//	}

	/** Returns a string form of code that, if executed, returns the
	 * receiver of for a dynamic call. This method is used by the
	 * method <code>dynamicInvocationMethod</code> to define a
	 * subclass-specific dynamic invocation method.
	 *
	 * @see #dynamicInvocationMethod
	 */
	protected abstract String receiver(/*@ non_null @*/ String className, 
			/*@ non_null @*/ String clazz, 
			/*@ non_null @*/ String receiver);

	/** 
	 * Returns true if an accessor (or a delegation method) is already
	 * generated for a model or spec_public field, <code>field</code>.
	 */
	protected /*@ pure @*/ boolean isAccessorGenerated(CField field) {
		return modelMethods.contains(field);
	}

	/** 
	 * Indicates that an accessor (or a delegation method) has been 
	 * generated for a model or spec_public field, <code>field</code>.
	 */
	//@ assignable modelMethods;
	protected void setAccessorGenerated(CField field) {
		modelMethods.add(field);
	}

	/** Returns true if dynamic calls are needed to access model,
	 * ghost, spec_public, and spec_protected fields declared in the
	 * given class <code>clazz</code>. The return value is true if the
	 * given class is not the same as the one being translated
	 * now. */
//	public static boolean dynamicCallNeeded(/*@ non_null @*/ CClass clazz) {
//		return clazz != currentCClass; // || currentCClass.isInterface();
//	}

	/** Returns true if the currently tranlated type is an interface. */
	public static boolean isInterface() {
		return currentCClass.isInterface();
	}

	/** Returns the identifier of the type currently being tranlated. */
	public static String ident() {
		return currentCClass.ident();
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** Target type declaration to be translated.
	 *
	 * <pre><jml>
	 * protected invariant typeDecl.getCClass() == currentCClass;
	 * </jml></pre>
	 */
	protected /*@ non_null @*/ JmlTypeDeclaration typeDecl;

	/** Variable generator for generating fresh variable names. */
	protected VarGenerator varGen;

	/** CClass of the target type declaration. */
	private static /*@ spec_protected non_null @*/ CClass currentCClass;

	/** True if a dynamic invocation method need be generated for the
	 * current type declaration as the result of the translation.
	 *
	 * @see #dynamicInvocationMethod
	 */
	public static boolean dynamicInvocationMethodNeeded = false;

	/** True if a specification inheritance method need be generated
	 * for the current type declaration as the result of the
	 * translation.
	 *
	 * @see TransExpression#visitJmlInvariantForExpression()
	 */
	public static boolean specInheritanceMethodNeeded = false;

	/**
	 * The set of model or spec_public field names whose access methods
	 * have alredy been generated.
	 *
	 * @see #translateRepresents(JmlRepresentsDecl[])
	 * @see #translateField(JmlFieldDeclaration)
	 */
	protected /*@ non_null @*/ Set modelMethods = new HashSet();
}
