/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id: JmlBinarySourceClass.java,v 1.6 2006/12/13 21:09:05 wdietl Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.util.ArrayList;
import java.util.Hashtable;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CCompilationUnitContextType;
import org.multijava.mjc.CField;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.FieldInfo;
import org.multijava.util.classfile.InnerClassInfo;
import org.multijava.util.classfile.MethodInfo;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a class read from a *.class file.  It is
 * primarily just a data structure, apart from methods for generating
 * the qualified name and for determining whether the member is
 * accessible from some class.
 *
 */
public class JmlBinarySourceClass extends JmlSourceClass {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class export from file. */
    public JmlBinarySourceClass( org.multijava.mjc.Main compiler, 
				 ClassInfo classInfo, File file ) {
	super( compiler,
	       getOuterClassFrom( classInfo.getName() ),
	       getHostFrom( classInfo.getName() ),
	       TokenReference.build(file, 0),
	       classInfo.getModifiers(),
	       getIdentFrom( classInfo.getName() ),
	       classInfo.getName(),
           CTypeVariable.EMPTY,
	       false,
	       false,
	       classInfo.isDeprecated() );

	this.setSuperClass( (classInfo.getSuperClass() == null) ?
			    null 
			    : CTopLevel.getTypeRep( classInfo.getSuperClass(),
						    true )
			    );

	CClassType[] interfaces = loadInterfaces( classInfo.getInterfaces() );

	FieldInfo[]	fields = classInfo.getFields();
	Hashtable	fields_H = null;
	CField[]	fields_V = null;

	if (fields.length <= 10) {
	    fields_V = new CField[fields.length];
	    for (int i = 0; i < fields.length; i++) {
		int mods = fields[i].getModifiers();
		String id = fields[i].getName().intern();
		CType typ = CType.parseSignature(fields[i].getSignature());
		JmlSourceField field 
		    = new JmlSourceField( new JmlMemberAccess(this, (long)mods&0xFFFFFFFFL),
					  id, typ, fields[i].isDeprecated()
					  );
		JmlBinaryField fieldAST 
		    = new JmlBinaryField( TokenReference.build(sourceFile(), 0),
					  field );
		field.setAST(fieldAST);
		fields_V[i] = field;
	    } 
	} else {
	    fields_H = new Hashtable(fields.length + 1, 1.0f);
      
	    for (int i = 0; i < fields.length; i++) {
		int mods = fields[i].getModifiers();
		String id = fields[i].getName().intern();
		CType typ = CType.parseSignature(fields[i].getSignature());
		JmlSourceField field 
		    = new JmlSourceField(new JmlMemberAccess(this, (long)mods&0xFFFFFFFFL),
					 id, typ, fields[i].isDeprecated()
					 );
		JmlBinaryField fieldAST 
		    = new JmlBinaryField(TokenReference.build(sourceFile(), 0),
					 field);
		field.setAST(fieldAST);
		fields_H.put(id, field);
	    }
	}

	MethodInfo[] methods = classInfo.getMultimethods();

	CCompilationUnitContextType cuc 
	    = compiler.createCompilationUnitContext( null, 
						     (CCompilationUnit) host()
						     );
	compiler.adoptCompilationUnitContext( cuc );
	JmlSourceMethod[] methods_A = new JmlSourceMethod[methods.length];
	for (int i = 0; i < methods.length; i++) {
	    JmlMemberAccess access 
		= new JmlMemberAccess(buildReceiverClass( this, methods[i] ),
				      this,
				      (long)methods[i].getModifiers()&0xFFFFFFFFL);
	    String id = methods[i].getName();
	    CType.MethodSignature mSig 
		= CType.parseMethodSignature(methods[i].getSignature());

	    methods_A[i] 
		= new JmlSourceMethod( access, id, 
				       mSig.returnType,
				       mSig.parameterTypes,
				       buildExceptionTypes( methods[i] ),
                                       CTypeVariable.EMPTY,
				       methods[i].isDeprecated(),
				       null, cuc, null );
	    JmlBinaryMethod methodAST 
		= new JmlBinaryMethod(TokenReference.build(sourceFile(), 0),
				      methods_A[i]);
	    methods_A[i].setAST(methodAST);
	}

	processInnerClassesAttr(classInfo.getInnerClasses());

	setCheckedInterfaces( interfaces );
	setCheckedMembers( fields_V, fields_H, methods_A );
	
	// -------------------------------------------------------------
	// construct set of directly visible types

	close( methods_A, new CClassType[0] );

	levelNumber = 9;
    }

    //---------------------------------------------------------------------
    // HELPER METHODS
    //---------------------------------------------------------------------

    protected static CClass buildReceiverClass(CClass host, 
					       MethodInfo methodInfo) 
    {
	CType.MethodSignature mSig = 
	    CType.parseMethodSignature(methodInfo.getSignature());
	CClassType recType = mSig.receiverType;
	if (recType == null || 
	    recType.qualifiedName().equals(host.qualifiedName())) {
	    // either a regular Java method signature with no explicit
	    // receiver, so use host; or the receiver is the same as
	    // the host class that is currently being built, so use
	    // host to avoid an infinite regress
	    return host;
	} else {
	    return recType.getCClass();
	}
    }

    private static CClassType[] buildExceptionTypes(MethodInfo methodInfo) {
	String[] exceptions = methodInfo.getExceptions();

	if (exceptions == null) {
	    return new CClassType[0];
	} else {
	    CClassType[] types = new CClassType[exceptions.length];

	    for (int i = 0; i < exceptions.length; i++) {
		types[i] = CTopLevel.getTypeRep( exceptions[i], true );
	    }
	    return types;
	}
    }

    /**
     * Loads the interfaces specified by the Strings in the argument
     * array (whether from other declarations in this compilation pass
     * or from *.class files.)
     *
     * @param	interfaces	the names of the interfaces to load
     * @return	an array of the types of the interfaces
     */
    protected CClassType[] loadInterfaces(String[] interfaces) {
	if (interfaces != null) {
	    CClassType[]	ret;
	    ret = new CClassType[interfaces.length];
	    for (int i = 0; i < interfaces.length; i++) {
		ret[i] = CTopLevel.getTypeRep(interfaces[i],true);
	    }
	    return ret;
	} else {
	    return CClassType.EMPTY;
	}
    }

    /**
     * Loads the inner classes specified by the info in the argument
     * array (whether from other declarations in this compilation pass
     * or from *.class files.)
     *
     * @param	inners		the info of the inner classes to load
     */
    protected final void processInnerClassesAttr(InnerClassInfo[] inners) {
	// the elements of inners fall into three categories: 
	// 1. nested and inner types of this, 
	// 2. self-referential nested type carrying additional modifier 
	//    information, and 
	// 3. other inner types visible within this, but whose
	//    information we currently ignore
	if (inners != null) {
	    ArrayList innerClassesAL = new ArrayList(inners.length);
	    for (int i = 0; i < inners.length; i++) {
		if (inners[i].getQualifiedName().equals(qualifiedName())) {
		    // category 2: self-referential nested type, grab
		    // its modifiers
		    access().setModifiers( access().modifiers() 
					   | inners[i].getModifiers() );
		    isAnonymous = inners[i].isAnonymous();
		    isMember = inners[i].isMember();
		} else if(inners[i].outerClassName().equals(qualifiedName())) {
		    // category 1: add to innerClasses of this
		    innerClassesAL.add(
			CTopLevel.getTypeRep( inners[i].getQualifiedName(),
					      true ));
		} // else category 3, ignored
	    }
	    CClassType[] innerClasses = new CClassType[innerClassesAL.size()];
	    innerClassesAL.toArray(innerClasses);
	    setInnerClasses( innerClasses );
	    
	}
    }

    /**
     * Returns the surrounding class for the inner class named by the argument.
     *
     * @param	clazz		the name of the inner class
     * @return	the class representing the surrounding class
     */
    private static CClass getOuterClassFrom(String clazz) {
	int index = clazz.lastIndexOf("$");
	
	return index == -1 ? 
	    null : CTopLevel.loadClass( clazz.substring( 0, index ) );	
    }

    /**
     * Returns the host for the class named by the argument.
     *
     * @param	clazz		the name of the class
     * @return	the host for the named class
     */
    private static CMemberHost getHostFrom( String clazz ) {
	int index = clazz.lastIndexOf('/');
	return new CCompilationUnit( index == -1 ? "" : 
				     (clazz.substring(0, index) + "/") );
    }

    //---------------------------------------------------------------------
    // PUBLIC METHODS
    //---------------------------------------------------------------------

    /**
     * @return true if this class is anonymous
     */
    public boolean isAnonymous() {
	return isAnonymous;
    }

    /**
     * Indicates whether the class represented by this is a member
     * type.  A member type is a type that is declared inside another
     * type but that is not an anonymous class or a local type
     * declaration.  */
    public boolean isMember() {
	return isMember;
    }

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

    /**
     * Indicates whether the class represented by this is anonymous.  */
    private boolean isAnonymous;


    /**
     * Indicates whether the class represented by this is a member
     * type.  A member type is a type that is declared inside another
     * type but that is not an anonymous class or a local type
     * declaration.  */
    private boolean isMember;

}
