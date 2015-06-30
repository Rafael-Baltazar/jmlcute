/**
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
 * $Id: JInterfaceDeclarationWrapper.java,v 1.21 2007/02/08 14:05:49 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CInterfaceContextType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JClassBlock;
import org.multijava.mjc.JClassDeclaration;
import org.multijava.mjc.JClassFieldDeclarator;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JInitializerDeclaration;
import org.multijava.mjc.JInterfaceDeclaration;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JStatement;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a java interface in the syntax tree
 */
public class JInterfaceDeclarationWrapper extends JInterfaceDeclaration
    implements Constants
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs an interface declaration in the parsing tree.
     * @param	where		the line of this node in the source code
     * @param	modifiers	the list of modifiers of this class
     * @param	ident		the short name of this class
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
     * @see JMethodDeclarationType
     * @see JFieldDeclarationType
     * @see JClassBlock
     */
    public JInterfaceDeclarationWrapper( /*@ non_null */ TokenReference where,
					 long modifiers,
					 /*@ non_null */ String ident,
					 /*@ non_null */ CTypeVariable[] typevariables,
					 /*@ non_null */ CClassType[] interfaces,
					 /*@ non_null */ ArrayList methods,
					 /*@ non_null */ ArrayList inners,
					 /*@ non_null */ JPhylum[] fieldsAndInits,
					 /*@ nullable */ JavadocComment javadoc,
					 /*@ nullable */ JavaStyleComment[] comments,
					 boolean isRefinedType) {
	super( where, modifiers | ACC_INTERFACE | ACC_ABSTRACT,
	       ident, typevariables, interfaces, methods, inners, 
	       fieldsAndInits, javadoc, comments );
	this.isRefinedType = isRefinedType;
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Generates the signature object for this. This method is overridden
     * here to return an instance of {@link JmlSourceClass}.
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
    protected /*@non_null@*/  CSourceClass makeSignature(/*@non_null@*/ org.multijava.mjc.Main compiler,
        /*@ nullable */ CClass owner, /*@ non_null */ CMemberHost host, /*@non_null@*/ String prefix,
	boolean isAnon, boolean isMember)
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
     * Checks the basic interfaces to make sure things generally look
     * OK.  This pass gathers information about the type
     * signatures of everything (imported class files, classes being
     * compiled, methods, fields, etc...)  needed for the later
     * passes.  This information is stored in a CCompilationUnit
     * instance and instances of CMember that are bound to the AST.
     * Also adds things like the default constructor and the initializer
     * method to the AST (these are suppressed during pretty-printing).
     * This method is overridden herre to take account of instance model
     * fields.
     *
     * @param		context		the context in which this
     *					declaration appears
     * @exception	PositionedError	an error with reference to 
     *					the source file
     */
    public void checkInterface(/*@non_null@*/  CContextType context ) throws PositionedError {
	instanceInit = constructInitializers(false);
	if (instanceInit != null) {
            CInterfaceContextType self = 
                (CInterfaceContextType) createContext( context );
	    instanceInit.checkInterface(self);
	}
	super.checkInterface(context);
    }

    /**
     * Checks the static initializers created during the
     * checkInterface pass and performs some other checks that can be
     * performed simply before full blown typechecking.
     * This method is overridden herre to take account of instance model
     * fields.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if check fails */
    public void checkInitializers(/*@non_null@*/ CContextType context) 
        throws PositionedError {
	if (instanceInit != null) {
            CInterfaceContextType self = 
                (CInterfaceContextType) createContext( context );
	    instanceInit.checkInitializer( self );
	}

	super.checkInitializers( context );
    }

    /**
     * Builds and returns <code>static</code> initializers.  If there
     * is no <code>static</code>, this method returns <code>null</code>.  
     * This method is refined here to take into account of model fields.
     */
    protected /*@ nullable */ JInitializerDeclaration constructStaticInitializers() {
        return constructInitializers(true);
    }

    /**
     * Collects all initializers and builds a single method.
     * @param isStatic	build class (static) or instance initializers?
     */
    protected /*@ nullable */ JInitializerDeclaration constructInitializers(boolean isStatic) {
	ArrayList	elems = new ArrayList();
	boolean	needGen = false;
        for( int i = 0; i < fieldsAndInits.length; i++ ) {
            if ((fieldsAndInits[i] instanceof JClassBlock)) {
                if (isStatic) {
                    elems.add( fieldsAndInits[i] );
                    needGen = true;
                }
	    } else if ((fieldsAndInits[i] instanceof JFieldDeclarationType)) {
                JFieldDeclarationType fdecl = 
                    (JFieldDeclarationType) fieldsAndInits[i];
                if (isStatic == !hasFlag(fdecl.modifiers(), ACC_INSTANCE)) {
		    //needGen |= fdecl.needInitialization();
		    elems.add(
			new JClassFieldDeclarator(getTokenReference(), fdecl));
                }
	    }
        } // for

	JStatement[] stmts = new JStatement[elems.size()];
	elems.toArray( stmts );

	
	if (stmts.length > 0) {
	    return new JInitializerDeclaration(getTokenReference(),
					       new JClassBlock(
						     getTokenReference(), 
						     false, stmts ),
					       isStatic,
					       !needGen);
	} else {
	    return null;
	}
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

    // ----------------------------------------------------------------------
    // HELPER METHODS
    // ----------------------------------------------------------------------

    /** Returns <code>true</code> if the given filed declaration has 
     * the given modifier. */
    private boolean hasModifier(/*@non_null@*/ JFieldDeclarationType field, int mod) {
	return hasFlag(field.variable().modifiers(), mod);
    }

    protected boolean isRefinedType = false;
}
