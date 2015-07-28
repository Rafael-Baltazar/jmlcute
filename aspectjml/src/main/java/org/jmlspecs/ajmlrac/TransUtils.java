/*
 * Copyright (C) 2001 Iowa State University
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
 * $Id: TransUtils.java,v 1.48 2006/12/13 21:09:05 wdietl Exp $
 */

package org.jmlspecs.ajmlrac;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import org.jmlspecs.checker.JmlNumericType;
import org.jmlspecs.checker.JmlStdType;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CNumericType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.util.Utils;
import org.multijava.util.compiler.CompilationAbortedError;
import org.multijava.util.compiler.CompilationAbortedException;

/**
 * A utility class for translating JML annotated Java classes into 
 * RAC-enabled classes.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.48 $
 */
abstract public class TransUtils extends Utils implements RacConstants 
{
	/** Returns true if the modifiers indicate that we need to generate 
	 * specification-only accessor method.  The argument modifier is 
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

	/** Returns a string representation of the default value of the
	 * given type, <code>type</code>. The defualt value is determined
	 * according to JLS 4.4.5, e.g., <code>"false"</code> for boolean.
	 */
	public static String defaultValue(/*@ non_null @*/ CType type) {
		switch (getTypeID(type)) {
		case TID_BOOLEAN:
			return "false";
		case TID_BYTE:
			return "(byte) 0";
		case TID_SHORT:
			return "(short) 0";
		case TID_INT: 
			return "0";
		case TID_LONG: 
			return "0L";
		case TID_FLOAT:
			return "0.0f";
		case TID_DOUBLE:
			return "0.0d";
		case TID_CHAR:
			// ANTLR (or mjc) can't not handle unicode strings correctly,
			// so, for now we use "(char) 0" instead of "'\u0000'".
			return "(char) 0";
		default: // including JML \TYPE
			return "null";
		}
	}
	
	public static String defaultValue(/*@ non_null @*/ String type) {
		if(type.equals("boolean")){
			return "false";
		}
		else if(type.equals("byte")){
			return "(byte) 0";
		}
		else if(type.equals("short")){
			return "(short) 0";
		}
		else if(type.equals("int")){
			return "0";
		}
		else if(type.equals("long")){
			return "0L";
		}
		else if(type.equals("float")){
			return "0.0f";
		}
		else if(type.equals("double")){
			return "0.0d";
		}
		else if(type.equals("char")){
			// ANTLR (or mjc) can't not handle unicode strings correctly,
			// so, for now we use "(char) 0" instead of "'\u0000'".
			return "(char) 0";
		}
		else {
			// including JML \TYPE
			return "null";
		}
	}
	
	public static boolean isTypeReference(/*@ non_null @*/ String type) {
		if(type.equals("boolean")){
			return false;
		}
		else if(type.equals("byte")){
			return false;
		}
		else if(type.equals("short")){
			return false;
		}
		else if(type.equals("int")){
			return false;
		}
		else if(type.equals("long")){
			return false;
		}
		else if(type.equals("float")){
			return false;
		}
		else if(type.equals("double")){
			return false;
		}
		else if(type.equals("char")){
			return false;
		}
		else {
			// including JML \TYPE
			return true;
		}
	}

	/** Returns a string representation of a Java expression that
	 * denotes a wrapper object for the given variable,
	 * <code>ident</code> of type, <code>type</code>. E.g., <code>"new
	 * Boolean(x)"</code> if <code>ident</code> is <code>"x"</code>
	 * and <code>type</code> is boolean.
	 */
	public static /*@ non_null@*/  String wrappedValue(
			/*@ non_null @*/ CType type, 
			/*@ non_null @*/ String ident) 
	{
		if(type instanceof JmlNumericType) {
			type = ((JmlNumericType)type).javaType();
		}
		if (wrapperClasses.containsKey(type))
			return "new " + wrapperClasses.get(type) + "(" + ident + ")";
		else 
			return ident;
	}

	/** Returns <code>true</code> if the argument is a main method 
	 * declaration */
//	public static boolean isMain(JmlMethodDeclaration mdecl) 
//	{
//	JFormalParameter[] params = mdecl.parameters();
//	boolean hasRightParameters = params != null && params.length == 1;
//	if (hasRightParameters) {
//	CType type = params[0].getType();
//	hasRightParameters =  type.isArrayType() &&
//	CStdType.String.equals(((CArrayType)type).getBaseType());
//	}
//	return mdecl.modifiers() == (ACC_PUBLIC | ACC_STATIC) &&
//	mdecl.returnType() == CStdType.Void &&
//	"main".equals(mdecl.ident()) &&
//	hasRightParameters;
//	}

	/** Returns the name of an old-expression evaluation method for the 
	 * class named <code>cls</code>.
	 *
	 * @param cls class name
	 * @param isStatic static or instance method?
	 *
	 * <pre><jml>
	 * requires cls != null;
	 * ensures \result != null;
	 * </jml></pre>
	 */
	public static String evalOldName(String cls, boolean isStatic) 
	{
		return MN_EVAL_OLD + (isStatic ? "static" : ("instance$" + cls));
	}

	/** Returns the name of an old-expression evaluation method for the 
	 * type declaration.
	 *
	 * @param tdecl type declaration
	 * @param isStatic static or instance method?
	 *
	 * <pre><jml>
	 * requires tdecl != null;
	 * ensures \result != null;
	 * </jml></pre>
	 */
//	public static String evalOldName(JmlTypeDeclaration tdecl, 
//	boolean isStatic) {
//	return MN_EVAL_OLD + 
//	(isStatic ? "static" : ("instance$" + tdecl.ident()));
//	}

//	public static String evalOldName(CClassType ctype, boolean isStatic) {
//	return MN_EVAL_OLD + 
//	(isStatic ? "static" : ("instance$" + ctype.ident()));
//	}

//	public static String evalOldName(CClass clazz, boolean isStatic) {
//	return MN_EVAL_OLD + 
//	(isStatic ? "static" : ("instance$" + clazz.ident()));
//	}

//	/** Returns the name of invariant-like assertion check method. */
//	public static String invariantLikeName(String prefix, CClass clazz,
//	boolean forStatic) {
//	return prefix + 
//	(forStatic ? "static" : ("instance$" + clazz.ident()));
//	}

//	/** Returns the name of invariant-like assertion check method. *//*
//	public static String subtypeConstraintName(String prefix, CClass clazz,
//	boolean isWeakly) {
//	return prefix + SubtypeConstraintMethod.postfix(clazz, isWeakly);
//	}*/

	/**
	 * Returns the name to be used to make dynamic calls to assertion
	 * check methods of the given class. The returned is the
	 * fully-qualified name of the given class. However, if the class is
	 * an interface, it is the surrogate class's fully-qualified name.
	 */
	public static String dynamicCallName(CClass clazz) {
		String name = clazz.qualifiedName().replace('/','.');
		if (TransType.genSpecTestFile && beingTested(clazz)
				&& JmlRacGenerator.newPackageName != null 
				&& !JmlRacGenerator.newPackageName.equals("")) {
			name = JmlRacGenerator.newPackageName.replace('/','.') + "." + clazz.ident();
		}
//		if (clazz.isInterface()) {
//			name = name + "." + TN_SURROGATE + "_" + clazz.ident();
//		} 
		return name;
	}

//	/** Returns true if the class named is a spec file for which a test wrapper
//	is being created.
//	*/
	public static boolean beingTested(CClass clazz) {
		return clazz.equals(typeDecl.getCClass());
	}

	public static JTypeDeclarationType typeDecl = null; 

	/** Returns the string representation of the wrapper class for the
	 * given type. If the given type is a primitive type (e.g.,
	 * <code>int</code>), the standard wrapper class (e.g.,
	 * <code>"java.lang.Integer.TYPE"</code> is returned; otherwise,
	 * the type itself (e.g., <code>type.toString() + ".class"</code>)
	 * is returned.
	 *
	 * <pre><jml>
	 * requires type != null;
	 * ensures \result != null && \fresh(\result);
	 * </jml></pre>
	 *
	 * @see TransUtils#wrapValue(CType,String)
	 */
	public static String typeToClass(/*@ non_null @*/ CType type) {
		switch (getTypeID(type)) {
		case TID_BOOLEAN:
			return "java.lang.Boolean.TYPE";
		case TID_BYTE:
			return "java.lang.Byte.TYPE";
		case TID_CHAR:
			return "java.lang.Character.TYPE";
		case TID_SHORT:
			return "java.lang.Short.TYPE";
		case TID_INT: 
			return "java.lang.Integer.TYPE";
		case TID_LONG: 
			return "java.lang.Long.TYPE";
		case TID_FLOAT:
			return "java.lang.Float.TYPE";                        
		case TID_DOUBLE:
			return "java.lang.Double.TYPE";            
		case TID_VOID:
			return "java.lang.Void.TYPE";
		case TID_ARRAY:
			return type.toString() + ".class";
		case TID_TYPE: // JML's \TYPE
			// for performance reason, use a runtime cache
			return "rac$forName(\"java.lang.Class\")";
			//return "java.lang.Class.class";
		case TID_BIGINT:
		case TID_REAL:
			// Is this the right way? -YC
			return "rac$forName(\"" + type.toString() + "\")";
		case TID_CLASS:
			// for performance reason, use a runtime cache
			return "rac$forName(\"" + 
			type.getCClass().qualifiedName().replace('/', '.') +
			"\")";
		default:
			//@ unreachable; 
			throw new RuntimeException("Unreachable reached!");
		}
	}

	/** Returns a string representation of unwrapped value of <code>var</code>
	 * with respect to type <code>type</code>.
	 * E.g., <code>"((Integer)" + var + ").intValue()"</code>
	 * if <code>type</code> is <code>int</code>.
	 *
	 * @see #wrapValue(CType,String)
	 */
	protected static String unwrapObject(CType type, String var) {
		switch (getTypeID(type)) {
		case TID_BOOLEAN:
			return "((java.lang.Boolean)" + var + ").booleanValue()";
		case TID_BYTE:
			return "((java.lang.Byte)" + var + ").byteValue()";
		case TID_CHAR:
			return "((java.lang.Character)" + var + ").charValue()";
		case TID_DOUBLE:
			return "((java.lang.Double)" + var + ").doubleValue()";            
		case TID_FLOAT:
			return "((java.lang.Float)" + var + ").floatValue()"; 
		case TID_INT: 
			return "((java.lang.Integer)" + var + ").intValue()";
		case TID_LONG: 
			return "((java.lang.Long)" + var + ").longValue()";
		case TID_SHORT:
			return "((java.lang.Short)" + var + ").shortValue()";
		default: // including JML \TYPE
			return "((" + toString(type) + ")" + var + ")";
		}
	}

	/** Returns the string representation of wrapping the value of
	 * variable <code>var</code> of type <code>type</code> into an
	 * object. E.g., <code>"new java.lang.Integer(" + var +
	 * ")"</code> for type <code>int</code>.
	 *
	 * <pre><jml>
	 * requires type != null && var != null;
	 * ensures \result != null && \fresh(\result);
	 * </jml></pre>
	 *
	 * @see #unwrapObject(CType,String)
	 */
	public static String wrapValue(CType type, String var) {
		switch (getTypeID(type)) {
		case TID_BOOLEAN:
			return "new java.lang.Boolean(" + var + ")";
		case TID_BYTE:
			return "new java.lang.Byte(" + var + ")";
		case TID_CHAR:
			return "new java.lang.Character(" + var + ")";
		case TID_DOUBLE:
			return "new java.lang.Double(" + var + ")";            
		case TID_FLOAT:
			return "new java.lang.Float(" + var + ")";                        
		case TID_INT: 
			return "new java.lang.Integer(" + var + ")";
		case TID_LONG: 
			return "new java.lang.Long(" + var + ")";
		case TID_SHORT:
			return "new java.lang.Short(" + var + ")";
		case TID_TYPE:  // for \TYPE
			return var; 
		default:
			return var;
		}
	}

	/**
	 * Returns the string representation of the given double value.  In
	 * particular, translates such special values as INFINITY, NaN,
	 * MIN_VALUE, and MAX_VALUE.
	 */
	public static String toString(double value) {
		return org.jmlspecs.ajmlrac.runtime.JMLChecker.toString(value);
	}

	/**
	 * Returns the string representation of the given float value.  In
	 * particular, translates such special values as INFINITY, NaN,
	 * MIN_VALUE, and MAX_VALUE.
	 */
	public static String toString(float value) {
		return org.jmlspecs.ajmlrac.runtime.JMLChecker.toString(value);
	}

	/**
	 * Returns the string representation of the given type. If the
	 * type is <code>JmlStdType.TYPE</code>, the result is 
	 * <code>"java.lang.Class"</code>; otherwise it is 
	 * <code>value.toString()</code>.
	 */
	public static String toString(CType value) {
		if (value == null) {
			return "java.lang.Object";
		} else if (value.getTypeID() == TID_TYPE) {
			return "java.lang.Class";
		} else if(value == JmlStdType.Bigint) {
			return "java.math.BigInteger";
		} else if(isBigintArray(value)) {
			return "java.math.BigInteger[]";
		} else if(value instanceof JmlNumericType) {
			return ((JmlNumericType)value).javaType().toString();
		} else {
			return value.getErasure().toString();
		}
	}

	public static int getTypeID(CType type) {
		if( type instanceof JmlNumericType) {
			type = ((JmlNumericType)type).javaType();
		}
		return type.getTypeID();
	}

	/**
	 * Returns a printable string representation for the given char
	 * value. E.g., "a" for 'a', "\\n" for '\n' and 
	 * "\\u0000" for '\u0000'.
	 */
	public static String toPrintableString(char c) {

		// printable ASCII char?
		if (('0' <= c && c <= '9') ||
				('A' <= c && c <= 'Z') ||
				('a' <= c && c <= 'z') ||
				("!#$%&()*+-.:;<=>?@[]^{|}~".indexOf(c) != -1)) {
			return new Character(c).toString();
		}

		// ASCII escape char?
		switch (c) {
		case '\b':
			return "\\b";
		case '\r':
			return "\\r";
		case '\t':
			return "\\t";
		case '\n':
			return "\\n";
		case '\f':
			return "\\f";
		case '\\':
			return "\\\\";
		case '\'':
			return "\\'";
		case '\"':
			return "\\\"";
		}

		// everything else, print as unicode
		String s = Integer.toHexString((int) c);
		switch (s.length()) {
		case 1: 
			return "\\u000" + s;
		case 2:
			return "\\u00" + s;
		case 3: 
			return "\\u0" + s;
		case 4:
			return "\\u" + s;
		}

		//@ unreachable;
		return "\\u0000";
	}

	/** Returns the name of the spec_public accessor for
	 * the method whose name is <code>ident</code>. */
	public static String specPublicAccessorName(String ident) {
		return MN_SPEC_PUBLIC + ident;
	}

	/** Returns the name of the spec_public accessor for
	 * the method whose name is <code>ident</code>. */
	public static String modelPublicAccessorName(CMethod meth) {
		if (meth.isPublic()) {
			return meth.ident();
		}
		return MN_SPEC_PUBLIC + meth.ident() + "$" + meth.owner().ident();
	}

//	/** Returns true if we use reflection for specification
//	* inheritance. */
//	public static boolean useReflection() {
//	return !Main.aRacOptions.noreflection();
//	}

	/** Returns true if the given type, <code>clazz</code>, is
	 * excluded from the set of types from which specifications can be
	 * inherited without using reflective method calls. All types from
	 * JDK except for those listed in
	 * <code>includedInInheritance</code> are excluded. Also excluded
	 * are thise listed in <code>excludedFromInheritance</code>.
	 *
	 * @see #excludedFromInheritance
	 * @see #includedInInheritance
	 */
	public static boolean excludedFromInheritance(CClass clazz) {
		if (clazz.qualifiedName().startsWith("java/")) {
			if (includedInInheritance == null) {
				initIncludedInInheritance();
			}
			return !includedInInheritance.contains(clazz);
		}
		return excludedFromInheritance.contains(clazz);
	}

	/** The set of types to be excluded, for specification
	 * inheritance, from making non-reflective calls to. */
	private static HashSet excludedFromInheritance = new HashSet();


	/** The set of types to which non-reflective calls are
	 * made for specification inheritance. The set should contain only
	 * interface types from JDK., i.e., whose package names starting
	 * with java. */
	private static HashSet includedInInheritance;

	/** Initializes the set of types to which non-reflective calls are
	 * made for specification inheritance. The set should contain only
	 * interface types from JDK., i.e., whose package names starting
	 * with java.
	 *
	 * <pre><jml>
	 * assignable includedInInheritance;
	 * ensures includedInInheritance != null;
	 * </jml></pre>
	 * @see #includedInInheritance
	 */
	private static void initIncludedInInheritance() {
		includedInInheritance = new HashSet();
		for (int i = 0; i < nonReflectiveTypes.length; i++) {
			try {
				includedInInheritance.add(
						CTopLevel.getTypeRep(nonReflectiveTypes[i],
								true).getCClass());
			}	
			catch (CompilationAbortedError e) {}
			catch (CompilationAbortedException e) {}
		}
		if (TransType.genSpecTestFile) {
			for (int i = 0; i < nonReflectiveTypes.length; i++) {
				try {
					includedInInheritance.add(
							CTopLevel.getTypeRep(nonReflectiveTypes[i],
									true).getCClass());
				}	
				catch (CompilationAbortedError e) {}
				catch (CompilationAbortedException e) {}
			}
		}
	}

	public static void initIncludedInInheritance(CClass cc) {
		if (includedInInheritance == null) {
			initIncludedInInheritance();
		}
		includedInInheritance.add(cc);
	}

	/**
	 * Returns a two-item string array which has the two parts in biginteger
	 * operation formula mapping the given binary operator <code>binOp</code>
	 *
	 * @see TransExpression#applyOperator(String v1, String v2, String binOp, CType type)
	 */
	public static String[] applyBigintBinOperator(String binOp)
	{
		String[] strArrayRet;

		String oper = binOp.trim();
		strArrayRet = new String[2];
		if(oper.equals("+")){
			strArrayRet[0] = ".add(";
			strArrayRet[1] = ")";
		}else if(oper.equals("-")) {
			strArrayRet[0] = ".subtract(";
			strArrayRet[1] = ")";
		}else if(oper.equals("*")) {
			strArrayRet[0] = ".multiply(";
			strArrayRet[1] = ")";
		}else if(oper.equals("/")) {
			strArrayRet[0] = ".divide(";
			strArrayRet[1] = ")";
		}else if(oper.equals("<")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") < 0";
		}else if(oper.equals("<=")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") <= 0";
		}else if(oper.equals(">")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") > 0";
		}else if(oper.equals(">=")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") >= 0";
		}else if(oper.equals("==")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") == 0";
		}else if(oper.equals("!=")) {
			strArrayRet[0] = ".compareTo(";
			strArrayRet[1] = ") != 0";
		}else if(oper.equals("%")) {
			strArrayRet[0] = ".remainder(";
			strArrayRet[1] = ")";
		}else if(oper.equals("<<")) {
			strArrayRet[0] = ".shiftLeft(";
			strArrayRet[1] = ")";
		}else if(oper.equals(">>")) {
			strArrayRet[0] = ".shiftRight(";
			strArrayRet[1] = ")";
		}else if(oper.equals(">>>")){
			fail("Shift operator \">>>\" is not supported for operands of type \\bigint.");
		}else if(oper.equals("&")) {
			strArrayRet[0] = ".and(";
			strArrayRet[1] = ")";
		}else if(oper.equals("|")) {
			strArrayRet[0] = ".or(";
			strArrayRet[1] = ")";
		}else if(oper.equals("^")) {
			strArrayRet[0] = ".xor(";
			strArrayRet[1] = ")";
		}else {
			fail("Internal error: unexpected binary operator " + oper + " applied to \\bigint operands.");
		}

		return strArrayRet;
	}

	/**
	 * Returns a string is the end part in biginteger
	 * operation formula mapping the given unary operator <code>unaryOp</code>
	 *
	 * @see TransExpression#applyOperator(String v, String unaryOp, CType type)
	 */
	public static String applyBigintUnOperator(String unaryOp)
	{
		String strRet="";

		String oper = unaryOp.trim();
		if( oper.equals("-") ) {
			strRet =".negate()";
		} else if( oper.equals("~") ) {
			strRet = ".not()";
		} else {
			fail("Internal error: unexpected unary operator " + oper + " applied to \\bigint operand.");
		}

		return strRet;
	}


	/**
	 * Returns a two-item string array which has the two parts in biginteger
	 * operation formula mapping the given destination type <code>typeDest</code>
	 * and source type <code>typeSource</code> in cast expression. the parm 
	 * <code>strTypeDest</code> is needed for in different class, the method "toString"
	 * is difined differently.
	 *
	 * @see RacPrettyPrinter#toString
	 * @see TransExpression#toString
	 * @see TransExpression#applyCast(String v, CType typeDest, CType typeVar)
	 */
	public static String[] applyBigintCast(CType typeDest, CType typeSource, String strTypeDest)
	{
		String[] strArrayRet;

		strArrayRet = new String[2];
		if( ((typeDest == JmlStdType.Bigint) && (typeSource == JmlStdType.Bigint)) || 
				((typeDest != JmlStdType.Bigint) && (typeSource != JmlStdType.Bigint)) ) {
			strArrayRet[0] = "(" + strTypeDest + ")";
			strArrayRet[1] = "";
		}else if(typeSource == JmlStdType.Bigint) {
			strArrayRet[0] = "(" + strTypeDest + ")";
			strArrayRet[1] = ".longValue()";
		} else { //(typeDest == JmlStdType.Bigint)
			strArrayRet[0] = "java.math.BigInteger.valueOf(";
			strArrayRet[1] = ")";
		}

		return strArrayRet;
	}

	/**
	 * Returns a string that represents the Java code that casts <code>strExpr</code>
	 * of type <code>typeExpr</code> to <code>typeSelf</code>.
	 * @see TransExpression#visitUnaryPromoteExpression
	 */
	public static String applyUnaryPromoteExpression(CType typeSelf, CType typeExpr, String strExpr)
	{
		String strRet="";

		if( (typeSelf == JmlStdType.Bigint) && (typeExpr != JmlStdType.Bigint) ) {
			strRet = "java.math.BigInteger.valueOf(" + strExpr + ")";
		} else {
			strRet = "(" + toString(typeSelf) + ") " + strExpr;
		}

		return strRet;
	}

	/**
	 * Returns a string that represents the Java code that convert the parm 
	 * <code>strVar</code> to its corresponding value of BigInteger which is
	 * the other parm <code>typ</code> indicate the type of <code>strVar</code>.
	 */
	public static String numberToBigint(String strVar, CType type)
	{
		String strRet="";

		if(type instanceof CNumericType) {
			if(type == JmlStdType.Bigint) {
				strRet = strVar;
			}else{
				strRet = "java.math.BigInteger.vauleOf(" + strVar + ")";
			}
		}else {
			fail("Cannot convert an expression of type " + toString(type) + "to " + JmlStdType.Bigint);
		}

		return strRet;
	}

	/**
	 * Returns a two-item string array which has the two parts in biginteger
	 * operation formula mapping the given source type <code>typeSource</code>
	 * which is a \bigint or numerical type to destination number type 
	 * <code>typeNumber</code> which is a numerical type.cast expression. the parm 
	 * <code>strTypeDest</code> is needed for in different class, the method "toString"
	 * is difined differently.
	 *
	 * @see TransExpression#applyArrayAccessExpression
	 * @see RacPrettyPrinter#visitArrayAccessExpression
	 */
	public static String[] applyBigintToNumber(CType typeSource, CType typeNumber)
	{
		String[] strArrayRet = new String[2];

		if(typeSource instanceof CNumericType) {
			if(typeSource == JmlStdType.Bigint) {
				if(typeNumber == CStdType.Integer){
					strArrayRet[0] = "(";
					strArrayRet[1] = ").intValue()";
				}else if(typeNumber == CStdType.Long){
					strArrayRet[0] = "(";
					strArrayRet[1] = ").longValue()";
				}else{
					fail("Internal error: unexpected number type " + typeNumber + " applied to \\bigint convertion.");
				}
			}else {
				strArrayRet[0] = "";
				strArrayRet[1] = "";
			}
		}else {
			fail("Cannot convert an expression of type " + toString(typeSource) + "to " + JmlStdType.Bigint);
		}

		return strArrayRet;
	}


	/**
	 * Returns a two-item string array which has the two parts in out of range
	 * assertion code for translating \bigint to number.
	 *
	 * @see TransExpression#applyArrayAccessExpression
	 * @see RacPrettyPrinter#visitArrayAccessExpression
	 */
	public static String[] createBigintConvertionAssertion(CType typeSource, CType typeDest)
	{
		String strNumberMax, strMethodNum;
		String[] strArrayRet = new String[2];

		if(typeSource != JmlStdType.Bigint) {
			strArrayRet[0] = "";
			strArrayRet[1] = "";
		} else {
			if(typeDest == CStdType.Integer) {
				strNumberMax = "Integer.MAX_VALUE";
				strMethodNum = "intValue()";
			} else if(typeDest == CStdType.Long) {
				strNumberMax = "Long.MAX_VALUE";
				strMethodNum = "longValue()";
			}else{
				strNumberMax = "";
				strMethodNum = "";
				fail("Internal error: unexpected number type " + typeDest + " applied to \\bigint convertion.");
			}

			strArrayRet[0] = "\tif( (";
			strArrayRet[1] = ")." + strMethodNum + " > " + strNumberMax + " ) {\n"
			+ "\tthrow new RuntimeException(\"Out of range while convert \\bigint to number.\");\n"
			+ "\t}\n";
		}

		return strArrayRet;
	}

	/**
	 * To check if the type is "\bigint[]"
	 */
	public static boolean isBigintArray(CType type)
	{
		return (type instanceof org.multijava.mjc.CArrayType &&
				((org.multijava.mjc.CArrayType)type).getBaseType() instanceof JmlNumericType);
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** An array of type names to which non-reflective calls would be
	 * made for specification inheritance. This array should contain only
	 * interface types from JDK, e.g., those found in the directory
	 * <code>JML2/specs/java</code>. */    
	private static final String[] nonReflectiveTypes = {
		"java/lang/Comparable",
		"java/util/Collection",
		"java/util/Enumeration",
		"java/util/Iterator",
		"java/util/List",
		"java/util/ListIterator",
		"java/util/Map",
		"java/util/Observer",
		"java/util/Set",
		"java/util/SortedMap",
		"java/util/SortedSet",
		"java/lang/CharSequence", // only for JDK 1.4
	};

	/** An array of type names to which non-reflective calls would be
	 * made for specification inheritance. This array should contain only
	 * refinement types from JDK, e.g., those found in the directory
	 * <code>JML2/specs/java</code>. */    
//	private static final String[] nonReflectiveRefinementTypes = {
//		"java/util/AbstractCollection",
//		"java/util/AbstractList",
//		"java/util/Vector",
//		"java/lang/Number",
//	};

	/** Mapping from primitive types to their wrapper classes */
	private static Map wrapperClasses = new HashMap();
	static {
		wrapperClasses.put(CStdType.Boolean, "java.lang.Boolean");
		wrapperClasses.put(CStdType.Byte, "java.lang.Byte");
		wrapperClasses.put(CStdType.Char, "java.lang.Character");
		wrapperClasses.put(CStdType.Double, "java.lang.Double");
		wrapperClasses.put(CStdType.Float, "java.lang.Float");
		wrapperClasses.put(CStdType.Integer, "java.lang.Integer");
		wrapperClasses.put(CStdType.Long, "java.lang.Long");
		wrapperClasses.put(CStdType.Short, "java.lang.Short");
	}
	
}
