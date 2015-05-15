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
 * This file is based on the original $Id: TransInterface.java,v 1.48 2006/12/13 21:09:05 wdietl Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.checker.JmlCommonOptions;
import org.jmlspecs.checker.JmlFieldDeclaration;
import org.jmlspecs.checker.JmlInterfaceDeclaration;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlRepresentsDecl;
import org.jmlspecs.checker.JmlSourceMethod;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CField;
import org.multijava.mjc.JMethodDeclarationType;

/**
 * A class for translating JML interface declarations. The translation
 * produces an inner class in the interface, called a <em>surrogate
 * class</em>.  The surrogate class takes the responsibility of
 * checking assertions of the interface and thus defines all the
 * assertion check methods for the interface.  This class supports the
 * <em>Template Method Pattern</em> laid out by the abstract
 * superclass {@link TransType}.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */

public class TransInterface extends TransType {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Construct a <code>TransInterface</code> object.
	 *
	 * @param interfaceDecl target interface declaration to be translated
	 */
	public TransInterface(JmlInterfaceDeclaration interfaceDecl) {
		super(interfaceDecl);
        this.interfaceDecl = interfaceDecl;
	}

	// ----------------------------------------------------------------------
	// TRANSLATION
	// ----------------------------------------------------------------------

	protected void translateInvariantAsPrecondition(){
		InvariantMethodAdviceAsPreconditionMethod m = new InvariantMethodAdviceAsPreconditionMethod(false, typeDecl, varGen);
		if(Main.aRacOptions.clientAwareChecking()){
			InvariantMethodAdviceAsPreconditionMethodClientAwareChecking mClientAwareChecking = new InvariantMethodAdviceAsPreconditionMethodClientAwareChecking(false, typeDecl, varGen);
			RacNode invariantMethod = (RacNode)mClientAwareChecking.generate();
			interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
		}
		else {
			if(Main.aRacOptions.callSiteInstrumentation()){
				InvariantMethodAdviceAsPreconditionMethodCallSite mCallSite = new InvariantMethodAdviceAsPreconditionMethodCallSite(false, typeDecl, varGen);
				RacNode invariantMethod = (RacNode)mCallSite.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
			}
			if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
				RacNode invariantMethod = (RacNode)m.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);	
			}	
		}
		
		// translating inner invariants - [[[hemr]]]
		ArrayList inners = typeDecl.inners();
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				m = new InvariantMethodAdviceAsPreconditionMethod(false, currentInnerType, varGen);

				if(Main.aRacOptions.clientAwareChecking()){
					InvariantMethodAdviceAsPreconditionMethodClientAwareChecking mClientAwareChecking = new InvariantMethodAdviceAsPreconditionMethodClientAwareChecking(false, typeDecl, varGen);
					RacNode invariantMethod = (RacNode)mClientAwareChecking.generate();
					interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
				}
				else {
					if(Main.aRacOptions.callSiteInstrumentation()){
						InvariantMethodAdviceAsPreconditionMethodCallSite mCallSite = new InvariantMethodAdviceAsPreconditionMethodCallSite(false, typeDecl, varGen);
						RacNode invariantMethod = (RacNode)mCallSite.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
					}
					if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
						RacNode invariantMethod = (RacNode)m.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);	
					}	
				}
			}
		}
	}

	protected void translateInvariantAsPostcondition(){
		InvariantMethodAdviceAsPostconditionMethod m = new InvariantMethodAdviceAsPostconditionMethod(false, typeDecl, varGen);
		if(Main.aRacOptions.clientAwareChecking()){
			InvariantMethodAdviceAsPostconditionMethodClientAwareChecking mClientAwareChecking = new InvariantMethodAdviceAsPostconditionMethodClientAwareChecking(false, typeDecl, varGen);
			RacNode invariantMethod = (RacNode)mClientAwareChecking.generate();
			interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
		}
		else {
			if(Main.aRacOptions.callSiteInstrumentation()){
				InvariantMethodAdviceAsPostconditionMethodCallSite mCallSite = new InvariantMethodAdviceAsPostconditionMethodCallSite(false, typeDecl, varGen);
				RacNode invariantMethod = (RacNode)mCallSite.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
			}
			if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
				RacNode invariantMethod = (RacNode)m.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);	
			}	
		}
		
		// translating inner invariants - [[[hemr]]]
		ArrayList inners = typeDecl.inners();
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				m = new InvariantMethodAdviceAsPostconditionMethod(false, currentInnerType, varGen);

				if(Main.aRacOptions.clientAwareChecking()){
					InvariantMethodAdviceAsPostconditionMethodClientAwareChecking mClientAwareChecking = new InvariantMethodAdviceAsPostconditionMethodClientAwareChecking(false, typeDecl, varGen);
					RacNode invariantMethod = (RacNode)mClientAwareChecking.generate();
					interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
				}
				else {
					if(Main.aRacOptions.callSiteInstrumentation()){
						InvariantMethodAdviceAsPostconditionMethodCallSite mCallSite = new InvariantMethodAdviceAsPostconditionMethodCallSite(false, typeDecl, varGen);
						RacNode invariantMethod = (RacNode)mCallSite.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);
					}
					if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
						RacNode invariantMethod = (RacNode)m.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)invariantMethod);	
					}	
				}
			}
		}
	}

	/** 
	 * Translates constraint clauses of this interface
	 * declaration. This method produces a couple of <em>constraint
	 * check methods</em>, one for the static constraints and the
	 * other for instance constraints.
	 * 
	 * <pre><jml>
	 * also
	 *   modifies hcMethod;
	 * </jml></pre>
	 */
	protected void translateConstraint() {
		ConstraintMethod m = new ConstraintMethod(false, typeDecl, varGen);
		if(Main.aRacOptions.clientAwareChecking()){
			ConstraintMethodClientAwareChecking mClientAwareChecking = new ConstraintMethodClientAwareChecking(false, typeDecl, varGen);
			RacNode constraintMethod = (RacNode)mClientAwareChecking.generate();
			interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
		}
		else{
			if(Main.aRacOptions.callSiteInstrumentation()){
				ConstraintMethodCallSite mCallSite = new ConstraintMethodCallSite(false, typeDecl, varGen);
				RacNode constraintMethod = (RacNode)mCallSite.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
			}
			if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
				RacNode constraintMethod = (RacNode)m.generate();
				interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
			}
		}
		
		// translating inner invariants - [[[hemr]]]
		ArrayList inners = typeDecl.inners();
		if(inners.size() > 0){
			for (Iterator iterator = inners.iterator(); iterator.hasNext();) {
				JmlTypeDeclaration currentInnerType = (JmlTypeDeclaration) iterator.next();
				m = new ConstraintMethod(false, currentInnerType, varGen);
				if(Main.aRacOptions.clientAwareChecking()){
					ConstraintMethodClientAwareChecking mClientAwareChecking = new ConstraintMethodClientAwareChecking(false, typeDecl, varGen);
					RacNode constraintMethod = (RacNode)mClientAwareChecking.generate();
					interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
				}
				else{
					if(Main.aRacOptions.callSiteInstrumentation()){
						ConstraintMethodCallSite mCallSite = new ConstraintMethodCallSite(false, typeDecl, varGen);
						RacNode constraintMethod = (RacNode)mCallSite.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
					}
					if(!Main.aRacOptions.noExecutionSiteInstrumentation()){
						RacNode constraintMethod = (RacNode)m.generate();
						interfaceDecl.addMember((JmlMethodDeclaration)constraintMethod);
					}
				}
			}
		}
	}

	/**
	 * Translates the given JML field declaration,
	 * <code>fieldDecl</code>, by specially handling final, model, model,
	 * spec_public, and spec_protected fields.
	 *
	 * <p>
	 * If this is a model field and has no accessor method generated yet
	 * (i.e., by <code>represents</code> clauses), generates the following 
	 * form of default model accessor method:
	 * 
	 * <pre>
	 * [[... model T m ...;]] ==
	 *   protected T m() {
	 *     throw new JMLNonExecutableException();
	 *   }
	 * </pre>
	 *
	 * <p> If the given declaration is a ghost field declaration,
	 * generates a pair of ghost field accessor methods (getter and
	 * setter), a private field for storing ghost values, and possibly
	 * an initialization block. The generated code has the following
	 * structure:
	 *
	 * <pre>
	 *  private [static] T v;
	 *  [static] {
	 *     v = initializer;
	 *  }
	 *  public [static] T ghost$v$C() {
	 *     return v;
	 *  } 
	 *  public [static] void ghost$v$C(T x) {
	 *     v = x;
	 *  } 
	 * </pre>
	 *
	 * The generated code is added to the surrogate class.
	 *
	 * <pre><jml>
	 * also
	 *   requires fieldDecl != null;
	 *   modifies modelMethods, interfaceDecl, newMethods;
	 * </jml></pre>
	 *
	 * @see #translateRepresents(JmlRepresentsDecl[])
	 * @see #ghostFieldAccessors(JmlFieldDeclaration)
	 * @see #modelMethods
	 */
	protected JmlFieldDeclaration translateField(
			JmlFieldDeclaration fieldDecl) 
	{
		JmlFieldDeclaration fdecl = super.translateField(fieldDecl);
		final CField field = fdecl.getField();
		final long modifiers = field.modifiers();
		if (hasFlag(modifiers, ACC_MODEL)) {
			// generate a default model field accessor if not 
			// already generated by represents clauses
			if (!isAccessorGenerated(field)) {
				// no need to issue a warning since represents 
				// clauses for model variables are usually declared 
				// in a concrete class. 
				addNewMethod(defaultModelFieldAccessor(field));
				setAccessorGenerated(field);
			}
		} 
		//			else if (hasFlag(modifiers, ACC_GHOST)) {
		//			addNewMethod(ghostFieldAccessors(fdecl));
		//		}
		// no special handling for spec_public or spec_protected fields
		// is needed because fields in interfaces are public (by default).

		return fdecl;
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
	 * <em>Pre (\pre) expression variables</em>.
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
	 * also
	 *   requires mdecl != null;
	 *   modifies newMethods, newFields;
	 * </jml></pre>
	 */
	protected void translateMethod(JmlMethodDeclaration mdecl)
	{
		if (mdecl.isModel()) {
			translateModelMethod(mdecl);
//			return;
		}

		TransMethod trans = new TransMethod(typeDecl, varGen);
		trans.perform(mdecl);
		//newMethods.addAll(trans.newMethods());

		// add newly created methods if any
		Iterator iter = trans.newMethods().iterator();
		while (iter.hasNext()){
			Object object = iter.next();
			//			JMethodDeclarationType jtd = (JMethodDeclarationType)object;
			typeDecl.addMember((JMethodDeclarationType)object);
		}	
		newFields.addAll(trans.newFields());
	}

	/**
	 * Translates the given model method (or constructor),
	 * <code>mdecl</code>. !FIXME!describe translation rules.
	 */
	//@ also assignable newMethods;
	protected void translateModelMethod(JmlMethodDeclaration mdecl) {
		//@ assume mdecl.isModel();

		// if not executable, we are done.
//		if (!mdecl.isExecutableModel() || mdecl.isConstructor()) {
		if (!mdecl.isExecutableModel()) {
			return;
		}
		
		mdecl.setModifiers(mdecl.modifiers() & (~ACC_MODEL));
		
		// for a protected and package-visible method, make it public
		// so that subclasses or other classes in the same package can
		// call it dynamically.
		long mod = mdecl.modifiers() & (~ACC_MODEL) & (~ACC_ABSTRACT);
		if (!(mdecl.isPublic() || mdecl.isPrivate())) {
			mod = (mod | ACC_PUBLIC) & (~ACC_PROTECTED);
		}
//		mdecl.setModifiers2(mdecl.modifiers2() | ACC2_RAC_METHOD);

		// build Java access method
		String nameAjmlc = mdecl.getMethod().owner().qualifiedName().replace('/', '.').replace("$", ".") + '.' + mdecl.getMethod().ident();
		JmlMethodDeclaration decl = JmlMethodDeclaration.makeInstance( // FIXME, This one can changed back to JmlMethodDeclaration if the member variable modifier2 is moved
				mdecl.getTokenReference(),
//				mod,
				(ACC_PRIVATE),
				mdecl.typevariables(),
				mdecl.returnType(),
//				TransUtils.modelPublicAccessorName(mdecl.getMethod()),
				nameAjmlc,
				mdecl.parameters(), 
				mdecl.getExceptions(),
				mdecl.body(), 
				new JavadocComment(""),
				null,
				null);

		decl.setModifiers2(decl.modifiers2() | ACC2_RAC_METHOD);
		if(mdecl.isStatic()){
			decl.setModifiers(decl.modifiers() | ACC_STATIC); 
		}
		
		String JMLHelperAnnotation =  ((Float.parseFloat(Main.aRacOptions.source()) > 1.4)? (((JmlSourceMethod)mdecl.getMethod()).isPure()? "\n@JMLHelper()":"") : "");

		// finally, add the accessor to the host class
		typeDecl.addMember(RacParser.parseMethod(
				"\n/** Generated by AspectJML to implement the model method " +
				mdecl.ident() + ". */"+JMLHelperAnnotation+"$0", decl));
	}

	/** Returns an access method for the given spec_public (or
	 * spec_protected) method declaration, <code>mdecl</code>. The
	 * returned method has the following code structure.
	 *
	 * <pre>
	 * public [static] T specPublic$m(x1, ..., xn) {
	 *   [return] m(x1, ..., xn);
	 * }
	 * </pre>
	 * 
	 * <pre><jml>
	 * requires mdecl.isSpecPublic() || mdecl.isSpecPublic();
	 * </jml></pre>
	 */
	//	private /*@ non_null @*/ JmlMethodDeclaration specPublicMethodAccessor(
	//			/*@ non_null @*/ JmlMethodDeclaration mdecl) {
	//		JFormalParameter[] parameters = mdecl.parameters();
	//		String ident = mdecl.ident();
	//		CType returnType = mdecl.returnType();
	//		boolean hasReturn = returnType != null && !returnType.isVoid();
	//
	//		// build arguments for delegation call of the form: (x1, ..., xn)
	//		StringBuffer args = new StringBuffer("(");
	//		for (int i = 0; i < parameters.length; i++) {
	//			if (i != 0)
	//				args.append(", ");
	//			args.append(parameters[i].ident());
	//		}
	//		args.append(")");
	//
	//		// build the body
	//		JBlock body = RacParser.parseBlock(
	//				"{\n" +
	//				(hasReturn ? "  return " : "  ") + ident + args + ";\n" +
	//		"}");
	//
	//		// build accessor method
	//		JMethodDeclaration m = new JMethodDeclaration(
	//				mdecl.getTokenReference(),
	//				ACC_PUBLIC | (mdecl.isStatic() ? ACC_STATIC : 0),
	//				CTypeVariable.EMPTY,
	//				returnType,
	//				specPublicAccessorName(ident),
	//				parameters,
	//				mdecl.getExceptions(),
	//				body,
	//				null,
	//				null);
	//
	//		// add javadoc and return the accessor
	//		return RacParser.parseMethod(
	//				"\n/** Generated by AspectJML for the " +
	//				(mdecl.isSpecPublic() ? "spec_public" : "spec_protected") +
	//				" method " + ident + ". */$0", m);
	//	}

	/**
	 * Finalizes the translation of this interface. This method generates 
	 * a <em>surrogate class</em> as an inner class of this interface.
	 *
	 * <pre><jml>
	 * also
	 *   modifies interfaceDecl, newMethods;
	 * </jml></pre>     
	 */
	//	protected void finalizeTranslation() {
	//
	//		// generate specification inheritance methods, if needed.
	//		if (specInheritanceMethodNeeded || // trans of \invariant_for
	//				(TransUtils.useReflection() 
	//						&& interfaceDecl.interfaces().length > 0)) {
	//			addNewMethod(assertionInheritanceMethod());
	//			specInheritanceMethodNeeded = false;
	//		}
	//		
	//		// concatenate all newly created methods, if any
	//		RacNode mdecls = null;
	//		for (Iterator i = newMethods.iterator(); i.hasNext(); ) {
	//			RacNode m = (RacNode)i.next();
	//			m.incrIndent();
	//			if (mdecls == null)
	//				mdecls = m;
	//			else
	//				mdecls = RacParser.parseMethod("$0$1", mdecls, m);
	//		}
	//
	//		// concatenate newly created fields if any
	//		StringBuffer code = new StringBuffer();
	//		for (Iterator i = newFields.iterator(); i.hasNext(); ) {
	//			code.append(i.next());
	//		}
	//		RacNode fdecls = null;
	//		if (code.length() > 0) {
	//			fdecls = RacParser.parseMethod(code.toString());
	//			fdecls.incrIndent();
	//		}
	//
	//		genSurrogateClass(fdecls, mdecls);
	//	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/**
	 * Generates a surrogate class for the interface declaration being
	 * translated. The generated surrogate class is added to the
	 * interface as a new member declaration. The surrogate class is
	 * responsible for checking assertions specified in the interface
	 * declaration, and thus declares all the assertion check methods
	 * for the interface. The surrogate class itself also implements
	 * the interface by delegating methods calls to implementing
	 * classes. Thus, (pure) method calls appearing in interface
	 * assertions are properly evaluated and checked by the
	 * implementing classes. The surrogate class is declared as a
	 * static inner class of the interface. The surrogate class has
	 * the following general structure.
	 *
	 * <pre>
	 * public class JmlSurrogate implements I, JMLSurrogate {
	 *   public JmlSurrogate(JMLCheckeble self) {
	 *     super(self);
	 *   }
	 *   public T1 m1(...) {
	 *     try {
	 *       return self.m1(...);
	 *     }
	 *     catch (java.lang.Throwable e) {
	 *       throw new java.lang.RuntimeException();
	 *     }
	 *   }
	 *   ...
	 *   public Tn mn(...) {
	 *     ...
	 *   }
	 *   private JMLCheckable self;
	 * }
	 * </pre>
	 * 
	 * where <code>I</code> is the name of the interface being
	 * translated. The interface JMLSurrogate defines properties that
	 * all surrogate classes have to implement, and the interface
	 * JMLCheckable defines properties for implementing classes. Both
	 * interfaces together define the minimal protocol for the
	 * surrogate class and the implementing class to communicate with
	 * each other for dynamic delegation.
	 *
	 * <pre><jml>
	 *  modifies interfaceDecl;
	 * </jml></pre>
	 *
	 * @param newFdecls field declarations to be added to the
	 * surrogate class. It may be null.
	 * @param newMdecls method declarations (e.g., assertion check
	 * methods) to be added to the surrogate class. It may be null.
	 */
	//	private void genSurrogateClass(RacNode newFdecls, RacNode newMdecls) 
	//	{
	//		// generate delegation methods implementing the target interface
	//		RacNode mdecls = concreteMethods();
	//		if (mdecls != null)
	//			mdecls.incrIndent();
	//
	//		String ident = interfaceDecl.ident();	
	//		StringBuffer code = new StringBuffer();
	//		
	//		code.append("\n");
	//		
	//		// add place holders ($0, $1, ...) for new fields and methods.
	//		code.append(surrogatePlaceHolders(newFdecls, newMdecls, mdecls));
	//
	//		// generate the surroage class and add it to the target interface
	//		Object[] args = surrogatePlaceValues(newFdecls, newMdecls, mdecls);
	//
	//		interfaceDecl.addMember(RacParser.parseMethod(code.toString(), args));
	//	}

	/** Returns a place holder string ($0...$n) for fields and methods
	 * of the surrogate class. 
	 *
	 * @see #surrogatePlaceValues(RacNode, RacNode, RacNode)
	 */
	//	protected String surrogatePlaceHolders(RacNode newFdecls,
	//			RacNode newMdecls,
	//			RacNode mdecls) {
	//		StringBuffer code = new StringBuffer();
	//		// fields used by assertion check methods
	//		code.append(newFdecls != null ? "$2" : ""); 
	//		// pre and postcondition check methods
	//		code.append(newMdecls != null ? "$1" : ""); 
	//		// delegation methods
	//		code.append(mdecls != null ? "$0" : "");  
	//		// invariant check methods
	//		code.append("$3");
	//		// constraint check methods
	//		code.append("$4");   
	//		return code.toString();
	//	}

	/** Returns an array of objects representing actual values for
	 * the place holder. 
	 *
	 * @see #surrogatePlaceHolders(RacNode, RacNode, RacNode)
	 */
	//	protected Object[] surrogatePlaceValues(RacNode newFdecls,
	//			RacNode newMdecls,
	//			RacNode mdecls) {
	//		return new Object[] {
	//				mdecls, newMdecls, newFdecls, invMethod, hcMethod,
	//		};
	//	}

	/** 
	 * Returns concrete method declarations, often called
	 * <em>delegation methods</em>, that implements the abstract
	 * methods declared in the interface (and its
	 * super-interfaces). The returned methods delegate calls to the
	 * corresponding methods in the implementing class. If there is no
	 * method declared in the interface, this method returns null as
	 * the result. Refer to the method <code>concreteMethod</code> for
	 * the general structure of the delegation method.
	 *
	 * @see #concreteMethod(CMethod)
	 * @see #genSurrogateClass(RacNode, RacNode)
	 */
	//	private RacNode concreteMethods()
	//	{
	//		CMethodSet.MethodArgsPair[] methods = interfaceDecl.getCClass().getInterfaceMethods();
	//		Set duplicateCheckSet = new HashSet(methods.length);
	//
	//		RacNode result = null;
	//		for (int i = 0; i < methods.length; i++) {
	//			// skip if static initializer
	//			if (methods[i].getMethod().ident() == JAV_STATIC_INIT)
	//				continue;
	//
	//			// check for duplication
	//			String sig = methods[i].getMethod().ident();
	//			CSpecializedType[] types = methods[i].getMethod().parameters();
	//			for (int j = 0; j < types.length; j++)
	//				sig = sig + ":" + types[j];
	//			if (!duplicateCheckSet.add(sig))
	//				continue;
	//
	//			// generate delegation method and append it to result
	//			JmlMethodDeclaration mdecl = concreteMethod(methods[i].getMethod());
	//			result = RacParser.parseMethod(result == null ? "$1" : "$0$1",
	//					result, mdecl);
	//		}
	//		return result;
	//	}

	/** 
	 * Returns a concrete (delegation) method that implements the
	 * abstract method declaration, <code>mdecl</code>.  The returned
	 * method delegates calls to the corresponding method in the
	 * implementing class. The general structure of the delegation
	 * method is as follows.
	 *
	 * <pre>
	 * public T1 m1(...) {
	 *   try {
	 *     return self.m1(...);
	 *   }
	 *   catch (java.lang.Throwable e) {
	 *     throw new java.lang.RuntimeException();
	 *   }
	 * }
	 * </pre>
	 *
	 * Since delegation methods are called only for evaluating
	 * interface assertions, all exceptions are caught and re-thrown
	 * as <code>RuntimeException</code>.
	 * 
	 * @see #concreteMethod(CMethod)
	 * @see #genSurrogateClass(RacNode, RacNode)
	 *
	 * <pre><jml>
	 * requires mdecl != null;
	 * ensures \result != null;
	 * </jml></pre>
	 */
	//	private JmlMethodDeclaration concreteMethod(CMethod mdecl) 
	//	{
	//		JFormalParameter[] formals = null;
	//		JBlock body = null;
	//		if ((mdecl.modifiers() & ACC_MODEL) != 0) {
	//			formals = new JFormalParameter[0];
	//			body = RacParser.parseBlock(
	//					"{\n" +
	//					"      throw JMLChecker.ANGELIC_EXCEPTION;\n" +
	//			"    }");
	//		} else {
	//			// generate a body of the form: 
	//			// { 
	//			//   try {
	//			//     [return] self.n(p1, ..., pn); 
	//			//   } 
	//			//   catch (java.lang.Throwable e$) {
	//			//     throw new java.lang.RuntimeException();
	//			//   }
	//			// }
	//			StringBuffer code = new StringBuffer("{\n");
	//			code.append("  try {\n");
	//			code.append("    ");
	//			if (!mdecl.returnType().isVoid()) {
	//				code.append("return ");
	//			}
	//			code.append("((" + typeDecl.ident() + ") self).")
	//			.append(mdecl.ident());
	//
	//			// arguments to delegation call
	//			code.append("(");
	//			CSpecializedType[] types = mdecl.parameters();
	//			formals = new JFormalParameter[types.length];
	//			for (int i = 0; i < types.length; i++) {
	//				if (i != 0)
	//					code.append(", ");
	//				code.append("p" + i);
	//				formals[i] = 
	//					new JFormalParameter(NO_REF, 0, types[i], "p" + i, false);
	//			}
	//			code.append(");\n");
	//
	//			code.append("  }\n");
	//			code.append("  catch (java.lang.Error e$) {\n");
	//			code.append("    throw JMLChecker.ANGELIC_EXCEPTION;\n");
	//			code.append("  }\n");
	//			code.append("  catch (java.lang.Throwable e$) {\n");
	//			code.append("    throw JMLChecker.ANGELIC_EXCEPTION;\n");
	//			code.append("  }\n");
	//			code.append("}");
	//
	//			// !FIXME! mjc code generation error
	//			if ("clone".equals(mdecl.ident()) && mdecl.parametersSize() == 0) {
	//				code = new StringBuffer(
	//						"{\n" +
	//						"  // to avoid mjc's code generation error!\n" +
	//						"  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
	//				"}");
	//			}
	//			body = RacParser.parseBlock(code.toString());
	//		}
	//
	//		// new JavaDocComment(String) org.multijava.javadoc.
	//		return JmlMethodDeclaration.makeInstance(NO_REF, ACC_PUBLIC, 
	//				mdecl.getTypeVariable(), mdecl.returnType(), mdecl.ident(), formals,
	//				new CClassType[0], // mdecl.throwables()
	//				body, null, null, null);
	//	}

	/** 
	 * Returns a default accessor method for a model field, 
	 * <code>field</code>. A default model field access method performs
	 * a dynamic call to the corresponding model field access method of
	 * the implementing class and has the following form:
	 * <pre>
	 *  public [static] T model$n() {
	 *    String cn = self.getClass().getName();
	 *    Object obj = rac$invoke(cn, self, "model$n", null, null);
	 *    return unwrapObject(T, obj);
	 *  }
	 * </pre>
	 */
	private JmlMethodDeclaration defaultModelFieldAccessor(CField field)
	{
//		dynamicInvocationMethodNeeded = true;
//
//		// String mod = field.isStatic() ? "static " : "";
//		CType type = field.getType();
//		String mn = MN_MODEL + field.ident() + "$" + field.owner().ident();
//		if (field.isStatic()) {
//			return RacParser.parseMethod(
//					"\n\n/** Generated by JML to access the model field " + 
//					field.ident() + ". */\n" +
//					"public static " + toString(type) + " " + mn + "() {\n" +
//					"  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
//			"}\n");
//		} else {
//			return RacParser.parseMethod(
//					"\n\n/** Generated by JML to access the model field " + 
//					field.ident() + ". */\n" +
//					"public " + toString(type) + " " + mn + "() {\n" +
//					"  java.lang.String cn = self.getClass().getName();\n" +
//					"  java.lang.Object obj = rac$invoke(cn, self, \"" + mn +
//					"\", null, null);\n" + 
//					"  return " + unwrapObject(type, "obj") + ";\n" +
//			"}\n");
//		}
		return RacParser.parseMethod("");
	}

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
	 * values and possibly an initializer block too. 
	 * 
	 * <pre>
	 *  private [static] T v;
	 *  [static] {
	 *     v = initializer;
	 *  }
	 * </pre>
	 *
	 * This method is overwritten here to combine code for accessors
	 * and the new private field declaration and return it as a single
	 * object. In the overwritten method, the new field declaration is
	 * piggybacked in the given field declaration for later
	 * pretty-printing (see RacPrettyPrinter.visitJmlFieldDeclaration).
	 *
	 * @see TransTypeForAjmlc#ghostFieldAccessors(JmlFieldDeclaration)
	 */
	//	protected JmlMethodDeclaration ghostFieldAccessors(
	//			JmlFieldDeclaration fdecl) 
	//	{
	//		JmlMethodDeclaration mdecl = super.ghostFieldAccessors(fdecl);
	//		mdecl = RacParser.parseMethod("$0$1", fdecl.assertionCode(), mdecl);
	//
	//		// clear the piggybacked code to prevent the new field
	//		// declaration from being printed in the interface
	//		// declaration; it becomes a member of the surrogate class for
	//		// the interface.
	//		fdecl.setAssertionCode(null);
	//		return mdecl;        
	//	}

	/** Adds a new method declaration, <code>mdecl</code>, to 
	 * the surrogate class to be generated in the finalization step of
	 * this translation.
	 */
	//@ also assignable newMethods;
	protected void addNewMethod(JmlMethodDeclaration mdecl) {
		newMethods.add(mdecl);
	}

	/** Returns a string form of code that, if executed, returns the
	 * receiver of for a dynamic call. This method is used by the
	 * method <code>dynamicInvocationMethod</code> to define a
	 * subclass-specific dynamic invocation method. 
	 *
	 * <pre><jml>
	 * also
	 *   ensures \result.equals(TN_JMLSURROGATE + ".getReceiver(" +
	 *                          clazz + ", " + receiver + ")");
	 * </jml></pre>
	 *
	 * @see TransTypeForAjmlc#dynamicInvocationMethod
	 */
	protected String receiver(String clsName, String clazz, String receiver) {
		return TN_JMLSURROGATE + ".getReceiver(" + clazz + ", " + 
		receiver + ")";
	}

	/** 
	 * Returns a method declaration implementing dynamic inheritance
	 * using the Java's reflection facility. The returned method is
	 * often called an <em>inheritance method</em>. The inheritance
	 * method makes dynamic invocations to assertion check methods,
	 * given an assertion check method's class name, method name,
	 * formal parameter types, and actual arguments. If the target
	 * assertion check method returns a boolean value, that value is
	 * returned; otherwise, true is returned. An exception thrown by
	 * the targe method is transparently propagated to the caller.
	 *
	 * <pre><jml>
	 * ensures \result != null;
	 * </jml></pre>
	 */
	//	protected JmlMethodDeclaration assertionInheritanceMethod() {
	//		return RacParser.parseMethod(
	//				"\n/** Generated by JML to make dynamic calls to an assertion\n" +
	//				" * check methoda, given its class name (className),\n" +
	//				" * method name (methodName), parameter types (types),\n" +
	//				" * and actual arguments (args).\n" +
	//				" * The reciever object <code>thisObj</code> and argument\n" +
	//				" * objects <code>args</code> are used for to make a dynamic\n" +
	//				" * call. If the assertion check method returns a boolean\n" +
	//				" * value, that value is returned; otherwise, true is returned.\n"+
	//				" * An exception thrown by the assertion method is\n" +
	//				" * transparently propagated to the caller. */\n" +
	//				"private static boolean rac$check(String className, " +
	//				"java.lang.Object thisObj,\n" +
	//				"  java.lang.String methodName, java.lang.Class types[], java.lang.Object args[]) {\n" +
	//				"  try {\n" +
	//				"    java.lang.Class clazz = rac$forName(className);\n" +
	//				"    java.lang.reflect.Method meth = " +
	//				"getMethod(clazz, methodName, types);\n" +
	//				"    java.lang.Object surObj = getReceiver(clazz, thisObj);\n" +
	//				"    java.lang.Object result = meth.invoke(surObj, args);\n" +
	//				"    return (result instanceof java.lang.Boolean) ?\n" +
	//				"      ((java.lang.Boolean) result).booleanValue() : true;\n" +
	//				"  }\n" +
	//				"  catch (java.lang.reflect.InvocationTargetException e) {\n" +
	//				"    java.lang.Throwable thr = e.getTargetException();\n" +
	//				"    if (thr instanceof java.lang.RuntimeException)\n" +
	//				"      throw (java.lang.RuntimeException) thr;\n" +
	//				"    else if (thr instanceof java.lang.Error)\n" +
	//				"      throw (java.lang.Error) thr;\n" +
	//				"    else\n" +
	//				"      throw new java.lang.RuntimeException(e.getMessage());\n" +
	//				"  }\n" +
	//
	//				// Ignore all other exceptions such as NoClassDefFoundError.
	//				"  catch (java.lang.Throwable e) {\n" +
	//				"    //e.printStackTrace();\n" +
	//				"    return false;\n" +
	//				"  }\n" +
	//				"}\n"
	//		);
	//	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** 
	 * Target interface to be translated.
	 * <pre><jml>
	 * private invariant interfaceDecl == (JmlInterfaceDeclaration)typeDecl;
	 * </jml></pre>
	 */
		private /*@ spec_protected non_null @*/ 
		JmlInterfaceDeclaration interfaceDecl;

	/** New mehtod declarations to be added to the surrogate class. */
	/*@ spec_protected @*/ private List newMethods = new LinkedList();

	/** New field declarations to be added to the surrogate class. */
	/*@ spec_protected @*/ private List newFields = new LinkedList();

	//	/** Invariant check methods for the current interface. */
	//	/*@ spec_protected @*/ private RacNode invMethod;
	//
	//	/** History constraint check methods for the current interface. */
	//	/*@ spec_protected @*/ private RacNode hcMethod;
	//
	//	/** Null token reference. */
	//	private static final TokenReference NO_REF = TokenReference.NO_REF;
}
