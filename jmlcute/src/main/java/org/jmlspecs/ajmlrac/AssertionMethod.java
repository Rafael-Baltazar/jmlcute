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
 * $Id: AssertionMethod.java,v 1.0 2009/01/15 05:11:33 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: AssertionMethod.java,v 1.9 2007/06/30 02:32:40 chalin Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jmlspecs.checker.JmlAbstractVisitor;
import org.jmlspecs.checker.JmlClassDeclaration;
import org.jmlspecs.checker.JmlConstraint;
import org.jmlspecs.checker.JmlFormalParameter;
import org.jmlspecs.checker.JmlInvariant;
import org.jmlspecs.checker.JmlMessages;
import org.jmlspecs.checker.JmlNode;
import org.jmlspecs.checker.JmlSourceField;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CBinaryField;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.util.compiler.TokenReference;

/**
 * An abstract class for generating <em>assertion check methods</em>
 * for specific kinds of assertions such as preconditions, normal and
 * exceptional postconditions, invariants and (history) constraints.
 * The generated assertion check methods inherit the superclass's
 * assertions by dynamically invoking the superclass's corresponding
 * assertion check methods. For example, the precondition check method
 * of a method, <code>m</code>, invokes dynamically the
 * <code>m</code>'s precondition method of the superclass if the
 * method <code>m</code> is overriden in the subclass.  In general,
 * the following rules are applied for inheriting assertions.
 *
 * <p>
 * <ul><li>
 * Method specifications such as preconditions and postconditions are 
 * inherited by the subclass, but only for intance (non-static) methods.
 * That is, class (static) method specifications are not inherited by
 * subclasses. In addition, method specifications for constructors are not
 * inherited by subclasses.
 * </li></ul>
 *
 * <ul><li>
 * Both static and non-static invariants are inherited by subclasses.
 * </li></ul>
 *
 * <ul><li>
 * Both static and non-static constraints are inherited by subclasses.
 * However, the inheritance of constraints is subjected to the
 * <em>strong</em> and <em>weak</em> behavioral subtyping, specified by
 * the <code>weakly</code> annotation in the <code>extends</code> clause.
 * Not implemented yet!
 * </li></ul>
 *
 * All inheritances are subjected to the accessibility; i.e., only public
 * and protected assertions are inherited. Not implemented yet!
 * </p>
 *
 * <p>
 * The class is implemented with a variant of the <em>Template Pattern</em>
 * [GoF95].
 * The abstract method <code>generate</code> is supposed to call the
 * methods <code>buildHeader</code> and <code>checker</code>,
 * respectively, to compose the header and the body of the assertion method.
 * The method <code>checker</code> calls the query method 
 * <code>canInherit</code> to decide whether to generate code for inheriting
 * specifications or not. The actual code for inheritance is generated
 * by calling the method <code>inheritAssertion</code>. 
 *
 * <pre>
 *  generate {abstract}
 *    buildHeader
 *    checker
 *      canInherit {abstract}
 *      inheritAssertion
 * </pre>
 * </p>
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */

public abstract class AssertionMethod extends TransUtils {
	// ----------------------------------------------------------------------
	// METHOD GENERATION
	// ----------------------------------------------------------------------

	/** Generates and returns an assertion checking method. Append to
	 * the body (<code>stmt</code>) code to check the inherited
	 * assertions if any, and code to throw an appropriate exception
	 * to notify an assertion violation if it happens at runtime.
	 * 
	 * @param stmt code to evaluate the assertions; the result is supposed
	 *             to be stored in the variable <tt>VN_ASSERTION</tt>. 
	 *             A <tt>null</tt> value means that no assertion is 
	 *             specified or the assertion is not executable.
	 */
	public abstract JMethodDeclarationType generate(RacNode stmt);




	/** Builds and returns a inter type method header as a string.
	 * 
	 * @param returnType return type
	 * @param name method name
	 * @param parameters formal parameters
	 */
	protected StringBuffer buildHeader(String returnType, String name,
			JFormalParameter[] parameters, CClassType[] exceptions) 
	{
		final StringBuffer code = new StringBuffer();

		// heading if any
		code.append("\n");
		if (javadoc != null) {
			code.append(javadoc);
		} else {
			code.append("/** Generated by JML to check assertions. */");
		}
		code.append("\npublic ");

		// return type and name
		if (isStatic)
			code.append("static ");
		code.append(returnType).append(" ").append(typeDecl.ident()+".").append(name);

		// foraml parameters
		code.append("(");
		if (parameters != null) {
			for (int i = 0; i < parameters.length; i++) {
				if (i != 0)
					code.append(", ");
				parameters[i].accept( new JmlAbstractVisitor() {
					public void	visitJmlFormalParameter(
							JmlFormalParameter self) {
						CType actualType = self.getType();
						String ident = self.ident();
						if( self.isFinal() ) {
							code.append("final ");
						}
						// FRioux - Experimental test for efficiency
						// In order to use the inner class approach, the params
						// have to be final.
//						else if(!Main.aRacOptions.oldSemantics()) {
							code.append("final ");
//						}
						code.append(TransUtils.toString(actualType));
						code.append(" ");
						code.append(ident);
					}
				});
			}
			if(parameters.length > 0){
				code.append(", final ").append(typeDecl.ident()).append(" rac$type");	
			}
			else{
				code.append("final ").append(typeDecl.ident()).append(" rac$type");	
			}
		}
		code.append(")");

		// checked-exceptions (throws list)
		/*if (exceptions != null) {
	    for (int i = 0; i < exceptions.length; i++) {
		code.append(i == 0 ? " throws " : ", ");
		code.append(exceptions[i].toString());
	    }
	}*/

		return code;
	}

	/** Indicates whether the generated assertion method should try 
	 * to dynamically inherit the corresponding assertion method of 
	 * the superclass. */
	protected abstract /*@ pure @*/ boolean canInherit();


	/**
	 * Returns true if the type being translated has an explicitly
	 * specified superclass.
	 */
	protected /*@ pure @*/ boolean hasExplicitSuperClass() {
		return (typeDecl instanceof JmlClassDeclaration) &&
		((JmlClassDeclaration)typeDecl).superName() != null;
	}

	/**
	 * Returns true if the type being translated has an explicitly
	 * MIDlet superclass.
	 */
	protected /*@ pure @*/ boolean hasExplicitMIDletSuperClass() {
		return (typeDecl instanceof JmlClassDeclaration) &&
		((JmlClassDeclaration)typeDecl).superName().equals("MIDlet");
	}
	
	protected String getProperCastType(String type){
		String result = null;
		if(type.equals("int")){
			result = "java.lang.Integer";
		}
		else if(type.equals("float")){
			result = "java.lang.Float";
		}
		else if(type.equals("boolean")){
			result = "java.lang.Boolean";
		}
		else if(type.equals("char")){
			result = "java.lang.Character";
		}
		else if(type.equals("short")){
			result = "java.lang.Short";
		}
		else if(type.equals("long")){
			result = "java.lang.Long";
		}
		else if(type.equals("byte")){
			result = "java.lang.Byte";
		}
		else{
			result = type;
		}
		return result;
	}
	
	protected String unboxing(String castType, String stmt){
		String result = null;
		if(castType.equals("java.lang.Integer")){
			result = "("+stmt+").intValue();\n";
		}
		else if(castType.equals("java.lang.Float")){
			result = "("+stmt+").floatValue();\n";
		}
		else if(castType.equals("java.lang.Boolean")){
			result = "("+stmt+").booleanValue();\n";
		}
		else if(castType.equals("java.lang.Character")){
			result = "("+stmt+").charValue();\n";
		}
		else if(castType.equals("java.lang.Short")){
			result = "("+stmt+").shortValue();\n";
		}
		else if(castType.equals("java.lang.Long")){
			result = "("+stmt+").longValue();\n";
		}
		else if(castType.equals("java.lang.Byte")){
			result = "("+stmt+").byteValue();\n";
		}
		else{
			result = stmt + ";\n";
		}
		return result;
	}
	
	private List temp(String[] preWords) {
		List privateFields = new ArrayList();
		List privateFieldsTmp = new ArrayList();
		List inheritedFields = getAllInheritedFields();
		Collection fields = typeDecl.getCClass().fields();
		
		//processing inherited fields
		for (Iterator iter = inheritedFields.iterator(); iter.hasNext();) {
			Object obj = iter.next();
			if (obj instanceof JmlSourceField){
				JmlSourceField varDef = (JmlSourceField) obj;
				for (int j = 0; j < preWords.length; j++) {
					if(!privateFieldsTmp.contains(varDef.ident()) && varDef.isPrivate() && varDef.ident().equals(preWords[j])){
						privateFields.add(varDef);
						privateFieldsTmp.add(varDef.getIdent());
					}
				}
		     }
			else if (obj instanceof CBinaryField){
				CBinaryField varDef = (CBinaryField) obj;
				for (int j = 0; j < preWords.length; j++) {
					if(!privateFieldsTmp.contains(varDef.ident()) && varDef.isPrivate() && varDef.ident().equals(preWords[j])){
						privateFields.add(varDef);
						privateFieldsTmp.add(varDef.getIdent());
					}
				}
			}	
		}
		
		//processing local fields
        for (Iterator iterator = fields.iterator(); iterator.hasNext();) {
			JmlSourceField varDef = (JmlSourceField) iterator.next();
			for (int j = 0; j < preWords.length; j++) {
				if(!privateFieldsTmp.contains(varDef.ident()) && varDef.isPrivate() && varDef.ident().equals(preWords[j])){
					privateFields.add(varDef);
					privateFieldsTmp.add(varDef.getIdent());
				}
			}
		}
     
		return privateFields;
	}
	
	protected List getPrivateFieldsOnPred(String pred){
		String [] preWords = pred.replace("(", "").replace(")", "").replace(";", "").replace(".", " ").split(" ");
		List privateFields = temp(preWords);
		return privateFields;
	}
	
	protected List getPrivateFieldsOnContextValues(String pred){
		String [] preWords = pred.replace("\"", " ").replace("+", " ").replace(".", " ").split(" ");
		List privateFields = temp(preWords);
		return privateFields;
	}

	protected List getAllInheritedFields(){
		Collection collect = null;
		List listFields = new ArrayList();

		try {
			CClassType superType = this.typeDecl.getCClass().getSuperType();
			collect = superType.getCClass().fields();
			CClassType [] interfaces = this.typeDecl.getCClass().getInterfaces();

			while (!superType.ident().equals("Object")){
				collect = superType.getCClass().fields();
				for (Iterator iter = collect.iterator(); iter.hasNext();) {
					listFields.add(iter.next());
				}

				superType = superType.getCClass().getSuperType();
			}

			for (int i = 0; i < interfaces.length; i++) {
				collect = interfaces[i].getCClass().fields();
				for (Iterator iter = collect.iterator(); iter.hasNext();) {
					listFields.add(iter.next());
				}
			}
		} catch (Exception e) {}

		return listFields;
	}

	/**
	 * Returns true if the given invariant clause is checkable. The
	 * clause is checkable if it is not a redundant specification or
	 * the command line option "noredundancy" is not turned on.
	 */
	private static boolean isCheckable(JmlInvariant inv) {
		return !inv.isRedundantly() || !Main.aRacOptions.noredundancy();
	}
	
	/**
     * Returns true if the given constraint clause is checkable. The
     * clause is checkable if it is not a redundant specification or
     * the command line option "noredundancy" is not turned on.
     */
    protected static boolean isCheckable(JmlConstraint cons) {
        return !cons.isRedundantly() || !Main.aRacOptions.noredundancy();
    }

	protected String getContextValuesForInvariant(boolean forStatic, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer contextValue = new StringBuffer("");
		List includedFields = new ArrayList();
		JmlInvariant [] invariants = typeDecl.invariants();

		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic)){
				continue;
			}	
			TransPostExpression2 transInv = new TransPostExpression2(mvarGen, null, mvarGen, false, invariants[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transInv.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");

			JFieldDeclarationType[] fields = typeDecl.fields();
			String fieldTmp = "";
			boolean hasFieldReferenceInPredicate = false;
			for (int l = 0; l < fields.length; l++) {
				JVariableDefinition varDef = fields[l].variable();
				for (int j = 0; j < preWords.length; j++) {
					if(varDef.ident().equals(preWords[j])){
						hasFieldReferenceInPredicate = true;
					}
				}
				
				if(this.typeDecl.isInterface() && hasFlag(varDef.modifiers(), ACC_MODEL) && varDef.isStatic()){
					boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
							&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
					if ( isNonNull) {
						fieldTmp = "non_null field '" + (this.typeDecl.getCClass().getJavaName()+".") + varDef.ident() + "'" + ("is \"+"+this.typeDecl.getCClass().getJavaName()+".JmlSurrogate_"+typeDecl.ident()+"."+varDef.ident());
					}
					else{
						fieldTmp = "nullable field '" + (this.typeDecl.getCClass().getJavaName()+".") + varDef.ident() + "'" + ("is \"+"+this.typeDecl.getCClass().getJavaName()+".JmlSurrogate_"+typeDecl.ident()+"."+varDef.ident());
					}
				}
				else{
					boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
							&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
					if ( isNonNull) {
						fieldTmp = "non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
					}
					else{
						fieldTmp = "nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
					}
				}

				if(hasFieldReferenceInPredicate){
					hasFieldReferenceInPredicate = false;
					if(contextValue.length() > 0){
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append("+\"").append("\\n").append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
					else{
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append(", when \\n");
							contextValue.append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
				}
			}	
		}	
		return (contextValue.length() > 0 ? contextValue.toString():"\"");
	}
	
	protected String getContextValuesForSpecificConstraint(JmlConstraint constraint, boolean forStatic, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer contextValue = new StringBuffer("");
		List includedFields = new ArrayList();

		TransPostExpression2 transConst = new TransPostExpression2(mvarGen, null, mvarGen, false, constraint.predicate(), null, this.typeDecl, "JMLInvariantError");
		String [] preWords = transConst.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");

		JFieldDeclarationType[] fields = typeDecl.fields();
		String fieldTmp = "";
		boolean hasFieldReferenceInPredicate = false;
		for (int l = 0; l < fields.length; l++) {
			JVariableDefinition varDef = fields[l].variable();
			for (int j = 0; j < preWords.length; j++) {
				if(varDef.ident().equals(preWords[j])){
					hasFieldReferenceInPredicate = true;
				}
			}
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
			if ( isNonNull) {
				fieldTmp = "non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
			}
			else{
				fieldTmp = "nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
			}

			if(hasFieldReferenceInPredicate){
				hasFieldReferenceInPredicate = false;
				if(contextValue.length() > 0){
					if (!includedFields.contains(fieldTmp)) {
						contextValue.append("+\"").append("\\n").append("\\t").append(fieldTmp);
						includedFields.add(fieldTmp);
					}
				}
				else{
					if (!includedFields.contains(fieldTmp)) {
						contextValue.append(", when \\n");
						contextValue.append("\\t").append(fieldTmp);
						includedFields.add(fieldTmp);
					}
				}
			}
		}	
		return (contextValue.length() > 0 ? contextValue.toString():"\"");
	}
	
	protected String getContextValuesForConstraint(boolean forStatic, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer contextValue = new StringBuffer("");
		List includedFields = new ArrayList();
		JmlConstraint [] constraints = typeDecl.constraints();

		for (int i = 0; i < constraints.length; i++) {
			if (!isCheckable(constraints[i]) ||
					(hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)){
				continue;
			}	
			
			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				continue;
			}
			
			TransPostExpression2 transConst = new TransPostExpression2(mvarGen, null, mvarGen, false, constraints[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transConst.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");

			JFieldDeclarationType[] fields = typeDecl.fields();
			String fieldTmp = "";
			boolean hasFieldReferenceInPredicate = false;
			for (int l = 0; l < fields.length; l++) {
				JVariableDefinition varDef = fields[l].variable();
				for (int j = 0; j < preWords.length; j++) {
					if(varDef.ident().equals(preWords[j])){
						hasFieldReferenceInPredicate = true;
					}
				}
				boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
						&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
				if ( isNonNull) {
					fieldTmp = "non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}
				else{
					fieldTmp = "nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}

				if(hasFieldReferenceInPredicate){
					hasFieldReferenceInPredicate = false;
					if(contextValue.length() > 0){
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append("+\"").append("\\n").append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
					else{
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append(", when \\n");
							contextValue.append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
				}
			}	
		}	
		return (contextValue.length() > 0 ? contextValue.toString():"\"");
	}
	
	protected String getVisibilityContextValuesForConstraint(boolean forStatic, VarGenerator varGen, long visibility){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer contextValue = new StringBuffer("");
		List includedFields = new ArrayList();
		JmlConstraint [] constraints = typeDecl.constraints();

		for (int i = 0; i < constraints.length; i++) {
			if (!isCheckable(constraints[i])
					|| (hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
					|| !(privacy(constraints[i].modifiers()) == visibility)){
				continue;
			}	
			
			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				continue;
			}
			
			TransPostExpression2 transConst = new TransPostExpression2(mvarGen, null, mvarGen, false, constraints[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transConst.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");

			JFieldDeclarationType[] fields = typeDecl.fields();
			String fieldTmp = "";
			boolean hasFieldReferenceInPredicate = false;
			for (int l = 0; l < fields.length; l++) {
				JVariableDefinition varDef = fields[l].variable();
				for (int j = 0; j < preWords.length; j++) {
					if(varDef.ident().equals(preWords[j])){
						hasFieldReferenceInPredicate = true;
					}
				}
				boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
						&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
				if ( isNonNull) {
					fieldTmp = "non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}
				else{
					fieldTmp = "nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}

				if(hasFieldReferenceInPredicate){
					hasFieldReferenceInPredicate = false;
					if(contextValue.length() > 0){
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append("+\"").append("\\n").append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
					else{
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append(", when \\n");
							contextValue.append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
				}
			}	
		}	
		return (contextValue.length() > 0 ? contextValue.toString():"\"");
	}
	
	protected String getVisibilityContextValuesForInvariant(boolean forStatic, long visibility, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer contextValue = new StringBuffer("");
		List includedFields = new ArrayList();
		JmlInvariant [] invariants = typeDecl.invariants();

		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic) ||
					 !(privacy(invariants[i].modifiers()) == visibility)){
				continue;
			}	
			TransPostExpression2 transInv = new TransPostExpression2(mvarGen, null, mvarGen, false, invariants[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transInv.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");

			JFieldDeclarationType[] fields = typeDecl.fields();
			String fieldTmp = "";
			boolean hasFieldReferenceInPredicate = false;
			for (int l = 0; l < fields.length; l++) {
				JVariableDefinition varDef = fields[l].variable();
				// could refer to other visibility
//				if(!(privacy(fields[l].modifiers()) == visibility)){
//					continue;
//				}
				for (int j = 0; j < preWords.length; j++) {
					if(varDef.ident().equals(preWords[j])){
						hasFieldReferenceInPredicate = true;
					}
				}
				boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[l].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
						&& !(hasFlag(fields[l].modifiers(), ACC_NULLABLE));
				if ( isNonNull) {
					fieldTmp = "non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}
				else{
					fieldTmp = "nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident());
				}

				if(hasFieldReferenceInPredicate){
					hasFieldReferenceInPredicate = false;
					if(contextValue.length() > 0){
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append("+\"").append("\\n").append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
					else{
						if (!includedFields.contains(fieldTmp)) {
							contextValue.append(", when \\n");
							contextValue.append("\\t").append(fieldTmp);
							includedFields.add(fieldTmp);
						}
					}
				}
			}	
		}	
		return (contextValue.length() > 0 ? contextValue.toString():"\"");
	}

	protected String getInvariantsTokenReference(boolean forStatic){
		StringBuffer tokenReference = new StringBuffer("");
		JmlInvariant [] invariants = typeDecl.invariants();
		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic)){
				continue;
			}	
			TokenReference tref = invariants[i].getTokenReference();
			if(tokenReference.length() > 0){
				tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.ident()+".java"+":"+tref.line()).append(")");	
			}
			else{
				tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.ident()+".java"+":"+tref.line()).append(")");
			}
		}
		return tokenReference.toString();
	}
	
	protected String getConstraintTokenReference(boolean forStatic){
		StringBuffer tokenReference = new StringBuffer("");
		JmlConstraint [] constraints = typeDecl.constraints();
		for (int i = 0; i < constraints.length; i++) {
			if (!isCheckable(constraints[i]) ||
					(hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)){
				continue;
			}	
			
			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				continue;
			}
			
			TokenReference tref = constraints[i].getTokenReference();
			if(tokenReference.length() > 0){
				tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.ident()+".java"+":"+tref.line()).append(")");	
			}
			else{
				tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.ident()+".java"+":"+tref.line()).append(")");
			}
		}
		return tokenReference.toString();
	}
	
	protected String getVisibilityConstraintTokenReference(boolean forStatic, long visibility){
		StringBuffer tokenReference = new StringBuffer("");
		JmlConstraint [] constraints = typeDecl.constraints();
		for (int i = 0; i < constraints.length; i++) {
			if (!isCheckable(constraints[i])
					|| (hasFlag(constraints[i].modifiers(), ACC_STATIC) != forStatic)
					|| !(privacy(constraints[i].modifiers()) == visibility)){
				continue;
			}
			// translate method-specific constraints
			if (!constraints[i].isForEverything()) {
				continue;
			}
			
			TokenReference tref = constraints[i].getTokenReference();
			if(tokenReference.length() > 0){
				tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");	
			}
			else{
				tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");
			}
		}
		return tokenReference.toString();
	}
	
	protected String getSpecificConstraintTokenReference(JmlConstraint constraint, boolean forStatic){
		StringBuffer tokenReference = new StringBuffer("");

		TokenReference tref = constraint.getTokenReference();
		if(tokenReference.length() > 0){
			tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");	
		}
		else{
			tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");
		}

		return tokenReference.toString();
	}
	
	protected String getVisibilityInvariantsTokenReference(boolean forStatic, long visibility){
		StringBuffer tokenReference = new StringBuffer("");
		JmlInvariant [] invariants = typeDecl.invariants();
		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic) ||
					!(privacy(invariants[i].modifiers()) == visibility)){
				continue;
			}	
			TokenReference tref = invariants[i].getTokenReference();
			if(tokenReference.length() > 0){
				tokenReference.append(", line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");	
			}
			else{
				tokenReference.append("line ").append(tref.line()).append(", ").append("character ").append(tref.column()).append(" ").append("(").append(this.typeDecl.getCClass().getJavaName()+".java"+":"+tref.line()).append(")");
			}
		}
		return tokenReference.toString();
	}

	protected String getContextValuesForDefaultInvariant(boolean forStatic, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer codeReference = new StringBuffer("");
		JFieldDeclarationType[] fields = typeDecl.fields();
		JmlInvariant [] invariants = typeDecl.invariants();
		List includedPreWords = new ArrayList();

		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic)){
				continue;
			}	
			TransPostExpression2 transInv = new TransPostExpression2(mvarGen, null, mvarGen, false, invariants[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transInv.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");
			for (int j = 0; j < preWords.length; j++) {
				if(!includedPreWords.contains(preWords[j])){
					includedPreWords.add(preWords[j]);
				}
			}
		}

		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			if ( varDef.isStatic() != forStatic ) {
				continue;
			}
			// build an expression of the form: x != null;
			TokenReference tref = fields[i].getTokenReference();

			if(codeReference.length() > 0){
				codeReference.append("\\n");
			}
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[i].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[i].modifiers(), ACC_NULLABLE));
			if(isNonNull && !includedPreWords.contains(varDef.ident())){
				codeReference.append("non_null for field '"+varDef.ident()+"'"+" <File \\\""+this.typeDecl.getCClass().getJavaName()+".java\\\", line "+tref.line()+", character "+tref.column()+" ("+this.typeDecl.getCClass().getJavaName()+".java:"+tref.line()+")>");
			}
		}
		return codeReference.toString();
	}
	
	protected String getVisibilityContextValuesForDefaultInvariant(boolean forStatic, long visibility, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		StringBuffer codeReference = new StringBuffer("");
		JFieldDeclarationType[] fields = typeDecl.fields();
		JmlInvariant [] invariants = typeDecl.invariants();
		List includedPreWords = new ArrayList();

		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic) ||
					!(privacy(invariants[i].modifiers()) == visibility)){
				continue;
			}	
			TransPostExpression2 transInv = new TransPostExpression2(mvarGen, null, mvarGen, false, invariants[i].predicate(), null, this.typeDecl, "JMLInvariantError");
			String [] preWords = transInv.stmtAsString().replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ").split(" ");
			for (int j = 0; j < preWords.length; j++) {
				if(!includedPreWords.contains(preWords[j])){
					includedPreWords.add(preWords[j]);
				}
			}
		}

		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			if ( (varDef.isStatic() != forStatic) || !(privacy(varDef.modifiers()) == visibility) ) {
				continue;
			}
			// build an expression of the form: x != null;
			TokenReference tref = fields[i].getTokenReference();

			if(codeReference.length() > 0){
				codeReference.append("\\n");
			}
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[i].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[i].modifiers(), ACC_NULLABLE));
			if(isNonNull && !includedPreWords.contains(varDef.ident())){
				codeReference.append("non_null for field '"+varDef.ident()+"'"+" <File \\\""+this.typeDecl.getCClass().getJavaName()+".java\\\", line "+tref.line()+", character "+tref.column()+" ("+this.typeDecl.getCClass().getJavaName()+".java:"+tref.line()+")>");
			}
		}
		return codeReference.toString();
	}

	protected String getFieldsValues(boolean forStatic){
		StringBuffer codeReference = new StringBuffer("");
		JFieldDeclarationType[] fields = typeDecl.fields();

		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			if ( varDef.isStatic() != forStatic ) {
				continue;
			}

			if(codeReference.length() > 0){
				codeReference.append("+\"").append("\\n").append("\\t");
			}
			else{
				codeReference.append("\\t");
			}
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[i].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[i].modifiers(), ACC_NULLABLE));
			if(isNonNull){
				codeReference.append("non_null field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident()));
			}
			else{
				codeReference.append("nullable field '" + (forStatic ? this.typeDecl.getCClass().getJavaName()+".":"this.") + varDef.ident() + "'" + (forStatic ? "is \"+"+this.typeDecl.getCClass().getJavaName()+"."+varDef.ident():" is \"+object$rac."+varDef.ident()));
			}
		}
		codeReference.insert(0,", when \\n");
		return codeReference.toString();
	}

	protected long privacy(long modifiers) {
		if (hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_PUBLIC))
			return ACC_PUBLIC;
		else if (hasFlag(modifiers, ACC_SPEC_PROTECTED | ACC_PROTECTED))
			return ACC_PROTECTED;
		else if (hasFlag(modifiers, ACC_PRIVATE))
			return ACC_PRIVATE;
		else
			return 0L; // package
	}
	
	protected void checkInvariantVisibilityRules(VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		JmlInvariant [] invariants = typeDecl.invariants();
		
		// check visibility rules
		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]))
				continue;
			// means that is not a public invariant
			if(privacy(invariants[i].modifiers()) != ACC_PUBLIC){
				TransPostExpression2 transInv = null;
				if (invariants[i].predicate() != null){
					transInv = 
							new TransPostExpression2(mvarGen, null, mvarGen, 
									false, 
									invariants[i].predicate(), null, this.typeDecl, "JMLInvariantError");
					// checking the missing rules for type specifications
					checkPrivacyRulesOKForTypeSpecs(transInv.stmtAsString(), privacy(invariants[i].modifiers()), invariants[i].getTokenReference());
				}
			}
		}
	}

	protected String combineInvariantsWithNonNull(boolean forStatic, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		JmlInvariant [] invariants = typeDecl.invariants();
		
		// conjoin all invariants
		JExpression root = null;
		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					(hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic))
				continue;
			JExpression p = new RacPredicate(invariants[i].predicate());
			root = root == null ? 
					p : new JConditionalAndExpression(org.multijava.util.compiler.TokenReference.NO_REF, 
							root, p);
		}

		// conjoin non-null annotations if any
		JFieldDeclarationType[] fields = typeDecl.fields();
		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[i].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[i].modifiers(), ACC_NULLABLE));
			if ( !isNonNull || 
					varDef.isStatic() != forStatic ) {
				continue;
			}
			// build an expression of the form: x != null;
			TokenReference tref = fields[i].getTokenReference();
			JExpression left = null; // left hand of expr != (e.g. x).

			// for a model field, build model$x$T() != null; otherwise
			// (including ghost field), build x != null.

			class CallExpr extends JMethodCallExpression {
				CallExpr(TokenReference ref, JExpression expr, CType type) {
					super(ref, expr, null);
					returnType = type;
				}

				public CType getType() {
					return returnType;
				}

				private CType returnType;
			};

//			if (hasFlag(varDef.modifiers(), ACC_MODEL)) {
//				String mn = MN_MODEL + varDef.ident() +"$"+ typeDecl.ident();
//				left = new CallExpr(tref, new JNameExpression(tref, mn),
//						varDef.getType());
//			} else {
				class CallExpr2 extends JMethodCallExpression {
					CallExpr2(TokenReference ref, JExpression expr, 
							CType type) {
						super(ref, expr, null);
						returnType = type;
					}

					public CType getType() {
						return returnType;
					}

					private CType returnType;
				};
				if(JmlRacGenerator.checking_mode == JmlRacGenerator.WRAPPER) {
					String fieldAcc = "_chx_get_" + varDef.ident();
					left = new CallExpr2(tref, 
							new JNameExpression(tref, fieldAcc), 
							varDef.getType());
				} else {
					left = new JLocalVariableExpression(tref, varDef);
				}
//			}

			// build expression of the form: x != null
			JExpression expr = new JEqualityExpression(tref, OPE_NE, left,
					new JNullLiteral(tref));

			// build rac predicate (for error reporting) and conjoin it
			expr = new RacPredicate(expr,
					"non_null for field '" + 
					fields[i].ident() + "'");
			root = root == null ? 
					expr : new JConditionalAndExpression(tref, expr, root);
		}
		TransPostExpression2 transInv = null;
		if (root != null){
			transInv = 
				new TransPostExpression2(mvarGen, null, mvarGen, 
						false, 
						root, null, this.typeDecl, "JMLInvariantError");
				AspectUtil.getInstance().currentCompilationUnitHasInvariants();
			return (this.processNonNullForInvariantPred(transInv.stmtAsString(), forStatic));
		}
		else{
			return "";	
		}
	}	

	protected String combineVisibilityInvariantsWithNonNull(boolean forStatic, long visibility, VarGenerator varGen){
		VarGenerator mvarGen = VarGenerator.forMethod(varGen);
		JmlInvariant [] invariants = typeDecl.invariants();
		
		// conjoin all invariants
		JExpression root = null;
		for (int i = 0; i < invariants.length; i++) {
			if (!isCheckable(invariants[i]) ||
					((hasFlag(invariants[i].modifiers(), ACC_STATIC) != forStatic)) ||
					!(privacy(invariants[i].modifiers()) == visibility))
				continue;
			JExpression p = new RacPredicate(invariants[i].predicate());
			root = root == null ? 
					p : new JConditionalAndExpression(org.multijava.util.compiler.TokenReference.NO_REF, 
							root, p);
		}

		// conjoin non-null annotations if any
		JFieldDeclarationType[] fields = typeDecl.fields();
		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			boolean isNonNull = (varDef.isDeclaredNonNull() || (TransUtils.isTypeReference(fields[i].getType().toString()) && Main.aRacOptions.defaultNonNull())) 
					&& !(hasFlag(fields[i].modifiers(), ACC_NULLABLE));
			if ( !isNonNull || 
					((varDef.isStatic() != forStatic)) || (!(privacy(varDef.modifiers()) == visibility)) ) {
				continue;
			}
			// build an expression of the form: x != null;
			TokenReference tref = fields[i].getTokenReference();
			JExpression left = null; // left hand of expr != (e.g. x).

			// for a model field, build model$x$T() != null; otherwise
			// (including ghost field), build x != null.

			class CallExpr extends JMethodCallExpression {
				CallExpr(TokenReference ref, JExpression expr, CType type) {
					super(ref, expr, null);
					returnType = type;
				}

				public CType getType() {
					return returnType;
				}

				private CType returnType;
			};

//			if (hasFlag(varDef.modifiers(), ACC_MODEL)) {
//				String mn = MN_MODEL + varDef.ident() +"$"+ typeDecl.ident();
//				left = new CallExpr(tref, new JNameExpression(tref, mn),
//						varDef.getType());
//			} else {
				class CallExpr2 extends JMethodCallExpression {
					CallExpr2(TokenReference ref, JExpression expr, 
							CType type) {
						super(ref, expr, null);
						returnType = type;
					}

					public CType getType() {
						return returnType;
					}

					private CType returnType;
				};
				if(JmlRacGenerator.checking_mode == JmlRacGenerator.WRAPPER) {
					String fieldAcc = "_chx_get_" + varDef.ident();
					left = new CallExpr2(tref, 
							new JNameExpression(tref, fieldAcc), 
							varDef.getType());
				} else {
					left = new JLocalVariableExpression(tref, varDef);
				}
//			}

			// build expression of the form: x != null
			JExpression expr = new JEqualityExpression(tref, OPE_NE, left,
					new JNullLiteral(tref));

			// build rac predicate (for error reporting) and conjoin it
			expr = new RacPredicate(expr,
					"non_null for field '" + 
					fields[i].ident() + "'");
			root = root == null ? 
					expr : new JConditionalAndExpression(tref, expr, root);
		}
		TransPostExpression2 transInv = null;
		if (root != null){
			transInv = 
				new TransPostExpression2(mvarGen, null, mvarGen, 
						false, 
						root, null, this.typeDecl, "JMLInvariantError");
				AspectUtil.getInstance().currentCompilationUnitHasInvariants();
			return (this.processNonNullForInvariantPred(transInv.stmtAsString(), forStatic));
		}
		else{
			return "";	
		}
	}
	
	protected void checkPrivacyRulesOKForTypeSpecs(String invariantPred, long typeSpecPrivacy, TokenReference typeSpecTokenRef){
		List inheritedFields = getAllInheritedFields();
		JFieldDeclarationType[] fields = typeDecl.fields();
		Pattern pattern = Pattern.compile("");
		Matcher matcher = pattern.matcher("");
		

		//processing inherited fields
		for (Iterator iter = inheritedFields.iterator(); iter.hasNext();) {
			Object obj = iter.next();
			if (obj instanceof JmlSourceField){
				JmlSourceField varDef = (JmlSourceField) obj;
				matcher.reset();
				pattern = Pattern.compile("(\\b)"+varDef.ident()+"(\\b)");
				matcher = pattern.matcher(invariantPred);
				if(matcher.find()){
					if(typeSpecPrivacy == ACC_PRIVATE) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
						else if (privacy(varDef.modifiers()) == 0L){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
					else if(typeSpecPrivacy == 0L) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
					else if(typeSpecPrivacy == ACC_PROTECTED) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
				}
			}	
			else if (obj instanceof CBinaryField){
				CBinaryField varDef = (CBinaryField) obj;
				matcher.reset();
				pattern = Pattern.compile("(\\b)"+varDef.ident()+"(\\b)");
				matcher = pattern.matcher(invariantPred);
				if(matcher.find()){
					if(typeSpecPrivacy == ACC_PRIVATE) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
						else if (privacy(varDef.modifiers()) == 0L){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
					else if(typeSpecPrivacy == 0L) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
					else if(typeSpecPrivacy == ACC_PROTECTED) {
						if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC)){
							JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
									varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
					  				JmlNode.privacyString(typeSpecPrivacy)});
							System.exit(0);
							break;
						}
					}
				}
			}	
		}
		
		//processing local fields
		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			matcher.reset();
			pattern = Pattern.compile("(\\b)"+varDef.ident()+"(\\b)");
			matcher = pattern.matcher(invariantPred);
			if(matcher.find()){
				if(typeSpecPrivacy == ACC_PRIVATE) {
					if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
						JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
								varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
				  				JmlNode.privacyString(typeSpecPrivacy)});
						System.exit(0);
						break;
					}
					else if (privacy(varDef.modifiers()) == 0L){
						JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
								varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
				  				JmlNode.privacyString(typeSpecPrivacy)});
						System.exit(0);
						break;
					}
				}
				else if(typeSpecPrivacy == 0L) {
					if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC | ACC_PROTECTED | ACC_SPEC_PROTECTED)){
						JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
								varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
				  				JmlNode.privacyString(typeSpecPrivacy)});
						System.exit(0);
						break;
					}
				}
				else if(typeSpecPrivacy == ACC_PROTECTED) {
					if(hasFlag(varDef.modifiers(), ACC_PUBLIC | ACC_SPEC_PUBLIC)){
						JmlRacGenerator.fail(typeSpecTokenRef, JmlMessages.FIELD2_VISIBILITY, new Object[] {
								varDef.ident(), JmlNode.privacyString( varDef.modifiers() ), 
				  				JmlNode.privacyString(typeSpecPrivacy)});
						System.exit(0);
						break;
					}
				}
			}

		}
	}

	private String processNonNullForInvariantPred(String invariantPred, boolean forStatic){
		List inheritedFields = getAllInheritedFields();
		JFieldDeclarationType[] fields = typeDecl.fields();

		//processing inherited fields
		for (Iterator iter = inheritedFields.iterator(); iter.hasNext();) {
			Object obj = iter.next();
			if (obj instanceof JmlSourceField){
				JmlSourceField varDef = (JmlSourceField) obj;
				if(invariantPred.contains("("+varDef.ident()+" != null)")){
					if(forStatic){
						invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "("+AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName())+"."+varDef.ident()+" != null)");
					}
					else{
						invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "(this."+varDef.ident()+" != null)");
					}
				}
			}	
			else if (obj instanceof CBinaryField){
				CBinaryField varDef = (CBinaryField) obj;
				if(invariantPred.contains("("+varDef.ident()+" != null)")){
					if(forStatic){
						invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "("+AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName())+"."+varDef.ident()+" != null)");
					}
					else{
						invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "(this."+varDef.ident()+" != null)");
					}
				}
			}	
		}

		//processing local fields
		for (int i = 0; i < fields.length; i++) {
			JVariableDefinition varDef = fields[i].variable();
			if(invariantPred.contains("("+varDef.ident()+" != null)")){
				if(varDef.isStatic()){
					invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "("+AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName())+"."+varDef.ident()+" != null)");
				}
				else{
					invariantPred = invariantPred.replace("("+varDef.ident()+" != null)", "(this."+varDef.ident()+" != null)");
				}
			}

		}
		return invariantPred;
	}

	/**
	 * @param invariant
	 * @param transPred
	 */
	protected String combineSpecCasesForInvariant(String instInv,
			String statInv) {
		StringBuffer result = new StringBuffer();

		result.append(instInv);	
		result.append(" && ");
		result.append(statInv);
		result.insert(0, "(");
		result.append(")");

		return result.toString();

	}
	
	protected String getQuantifierInnerClasses(String pred){
		StringBuffer result = new StringBuffer();
		result.append("");
		if(pred.contains(CN_RAC_QUANTIFIER_ID)){
			List ids = AspectUtil.getInstance().getQuantifierUniqueIDs();
			for (Iterator iterator = ids.iterator(); iterator.hasNext();) {
				String currentID = (String) iterator.next();
				if(pred.contains(currentID)){
					String qcode = AspectUtil.getInstance().getQuantifierInnerClassByID(currentID);
					result.append(qcode+"\n");
					
				}
			}
		}
//		System.out.println("#################################/*$BEGINquantifier1*/###############################################");
//		System.out.println();
//		System.out.println(AspectUtil.getInstance().getQuantifierInnerClassByID("/*$quantifier1*/"));
//		System.out.println();
//		System.out.println("#################################/*$ENDquantifier1*/###############################################");
//		System.out.println();
//		System.out.println();
//		System.out.println("#################################/*$BEGINquantifier2*/###############################################");
//		System.out.println();
//		System.out.println(AspectUtil.getInstance().getQuantifierInnerClassByID("/*$quantifier2*/"));
//		System.out.println();
//		System.out.println("#################################/*$ENDquantifier2*/###############################################");
//		System.out.println();
		return AspectUtil.changeThisOrSuperRefToAdviceRef(result.toString(), typeDecl);
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** target type declaration for generating assertion methods */
	protected JmlTypeDeclaration typeDecl;

	/** Name prefix of the method to be inherited, e.g., MN_CHECK_PRE */
	protected String prefix; 

	/** static-ness of assertion method */
	protected boolean isStatic; 

	/** name of assertion method */
	protected /*@ non_null @*/ String methodName;
	//@ protected invariant methodName.length() > 0;

	/** name of exception class to be thrown if assertions are violated.
	 */
	protected /*@ non_null @*/ String exceptionToThrow;
	//@ protected invariant exceptionToThrow.length() > 0;

	/** Javadoc comment to be added to the generated method. */
	protected /*@ nullable */ String javadoc;

	/** name of the target method for printing assertion violation error. */
	protected String methodIdentification;

	protected static final String SPEC_ERROR_MSG = " regarding specifications at \\n";

	protected static final String SPEC_EVAL_ERROR_MSG = "\"Invalid expression in \\\"";
	protected static final String CODE_ERROR_MSG = " regarding code at \\n";

}

