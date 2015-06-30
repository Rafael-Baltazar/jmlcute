
/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
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
 * $Id: JClassDeclarationWrapper.java,v 1.24 2007/02/08 14:05:49 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JClassDeclaration;
import org.multijava.mjc.JConstructorBlock;
import org.multijava.mjc.JConstructorDeclarationType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JStatement;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.TokenReference;

/**
 * A wrapper class to {@link JClassDeclaration} to implement JML-specific
 * typechecking.
 */
public class JClassDeclarationWrapper extends JClassDeclaration {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class declaration in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	modifiers	the list of modifiers of this class
     * @param	ident		the short name of this class
     * @param	superType       the name of this class's superclass
     * @param	interfaces	the names of this types's interfaces
     * @param	methods	        a list of JMethodDeclarationTypes giving the
     *				methods of this type
     * @param	inners	        a list of JTypeDeclarationTypes giving the
     *				inner classes (and interfaces) of this type
     * @param	fieldsAndInits	the fields and initializers of this type, 
     *				passed together because the order matters 
     *				for class and object initialization, members 
     *				of the array should be instances of 
     *				<code>JFieldDeclarationType</code> or 
     *				<code>JClassBlock</code>
     * @param	javadoc	        javadoc comments including whether this 
     *				type declaration is deprecated
     * @param	comments        regular java comments
     */
    public JClassDeclarationWrapper(TokenReference where,
				    long modifiers,
				    String ident,
				    CClassType superType,
				    CClassType[] interfaces,
				    ArrayList methods,
				    ArrayList inners,
				    JPhylum[] fieldsAndInits,
				    JavadocComment javadoc,
				    JavaStyleComment[] comments ) {
	super(where, modifiers, ident, CTypeVariable.EMPTY, superType, 
	      interfaces, methods, inners, fieldsAndInits, javadoc, comments );
	this.isRefinedType = false;
    }

    /**
     * Constructs a class declaration in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	modifiers	the list of modifiers of this class
     * @param	ident		the short name of this class
     * @param	superType 	the name of this class's superclass
     * @param	interfaces	the names of this types's interfaces
     * @param	methods	        a list of JMethodDeclarationTypes giving the
     *				methods of this type
     * @param	inners	        a list of JTypeDeclarationTypes giving the
     *				inner classes (and interfaces) of this type
     * @param	fieldsAndInits	the fields and initializers of this type, 
     *				passed together because the order matters 
     *				for class and object initialization, members 
     *				of the array should be instances of 
     *				<code>JFieldDeclarationType</code> or 
     *				<code>JClassBlock</code>
     * @param	javadoc	        javadoc comments including whether this 
     *				type declaration is deprecated
     * @param	comments        regular java comments
     */
    public JClassDeclarationWrapper(TokenReference where,
				    long modifiers,
				    String ident,
                    CTypeVariable[] typevariables,
				    CClassType superType,
				    CClassType[] interfaces,
				    ArrayList methods,
				    ArrayList inners,
				    JPhylum[] fieldsAndInits,
				    JavadocComment javadoc,
				    JavaStyleComment[] comments,
				    boolean isRefinedType) {
	super(where, modifiers, ident, typevariables, superType, 
	      interfaces, methods, inners, fieldsAndInits, javadoc, comments );
	this.isRefinedType = isRefinedType;
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------


    /**
     * Generates the signature object for this class declaration. 
     * This method overrides the inherited method to generate JML-specific
     * signature object, i.e., an instance of {@link JmlSourceClass}.
     *
     * @param compiler	the compiler instance for which this signature is 
     *			generated
     * @param owner	the class signature singleton for the logical outer 
     *			class of this, or null if this is a top level 
     *			declaration
     * @param host	the signature singleton of the context in which this
     *			is declared, a <code>CCompilationUnit</code> for 
     *			top-level declarations
     * @param prefix 	the prefix prepended to this declaration's
     *			identifier to achieve the fully qualified
     *			name, just the package name (using '/'
     *			separators) for top-level classes, package
     *			name plus $-delimited outer class names plus
     *			synthetic index for inner classes
     * @param isAnon	true if this is an anonymous class, in which 
     *			case the fully qualified name is just 
     *			<code>prefix</code> 
     * @param isMember	true if this is a member type, i.e., a nested type
     *			that is not a local type or an anonymous class
     */
    protected CSourceClass makeSignature(/*@non_null*/ org.multijava.mjc.Main compiler,
					 /*@nullable*/ CClass owner, /*@non_null*/ CMemberHost host, 
					 /*@non_null*/ String prefix, boolean isAnon, 
					 boolean isMember) 
    {

	String id;       // identifier of signature
	String qualName; // qualified name of signature
	if (isAnon) {
	    qualName = prefix;
	    int index = prefix.lastIndexOf('/');
	    id = index < 0 ? prefix : prefix.substring(index + 1);
	} else {
	    id = this.ident;
	    qualName = prefix + this.ident;
	}

	return new JmlSourceClass(compiler, owner, host,
				  getTokenReference(), modifiers, id, qualName, typevariables,
				  isAnon, isMember, isDeprecated());
    }

    /**
     * Returns true if this class declaration contains an 
     * explicit constructor declaration. 
     * This method is used by <code>checkInterface</code> 
     * to determine whether or not to create a default 
     * constructor for this type, i.e., when no explicit 
     * constructor is found. 
     *
     * In a refinement chain, if this declaration 
     * is not a '.java' file, then true is returned. 
     * (True is returned because the default constructor should 
     * only be automatically generated for the '.java' file.)
     */
    public boolean hasConstructor() {
	if ( inJavaFile() ) {
	    return super.hasConstructor();
	} else {
	    // do not generate a default constructor for 
	    // specification only (non-java) files.  
	    return true;
	}
    }

    /**
     * Builds an AST node representing the default constructor for this 
     * class.
     *
     * @return	an AST node
     */
    protected JConstructorDeclarationType constructDefaultConstructor() {
	long modifiers;
	CClass clz = getCClass();
	if (clz.isPublic()) {
	    modifiers = ACC_PUBLIC;
	} else if (clz.isProtected()) {
	    // Only nested classes may be protected
	    modifiers = ACC_PROTECTED;
	} else {
	    // Only nested classes may be private.  To allow outer
	    // classes to instantiate their nested classes we make the
	    // nested classes' constructors package-accessible.  See
	    // testcase/codegen/InnerProtected1.java for the javac 
	    // strategy, which is different.
	    modifiers = 0;
	}

	// the above code was copied from the superclass method!

	TokenReference where = getTokenReference();
	JConstructorBlock body = null;
	if ( inJavaFile() ) {
	    body = new JConstructorBlock( where, new JStatement[0] );
	} else {
	    body = new JConstructorBlock( where, null );
	}
	JConstructorDeclarationType defaultConstructor
	    = JmlConstructorDeclaration.makeInstance(
			where, modifiers, ident,
			JFormalParameter.EMPTY,
			CClassType.EMPTY,
			body, null, null, null );
	return defaultConstructor;
    }

    protected boolean inJavaFile() {
	JmlSourceClass self = (JmlSourceClass) getCClass();
	return self.inJavaFile();
    }

    public int compareTo(/*@ non_null @*/ Object o) throws ClassCastException {
	// If a change is required in this method, then the same 
	// change is probably required in JClassDeclarationWrapper.
	// Here is a case where multiple inheritance would have been 
	// useful and a static method would not have been necessary!

	if (o instanceof JClassDeclaration) {
	    JClassDeclaration other = (JClassDeclaration) o;
	    return this.getCClass().compareTo( other.getCClass() );
	}
	int res = super.compareTo(o);
	return res;
    }

    public boolean isRefinedType() { return isRefinedType; }
    
    protected boolean isRefinedType = false;
}
