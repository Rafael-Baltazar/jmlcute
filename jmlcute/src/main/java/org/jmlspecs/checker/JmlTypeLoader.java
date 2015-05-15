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
 * $Id: JmlTypeLoader.java,v 1.42 2004/12/30 00:28:26 cheon Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.jmlspecs.util.classfile.JmlClassInfoCreator;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.Main.Task;
import org.multijava.mjc.TypeLoader;
import org.multijava.util.MjcHashRelation;
import org.multijava.util.classfile.ClassFileReadException;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.ClassPath;

/**
 * This class acts as a symbol table and a cache for types, type
 * signatures, and external generic functions.  It includes methods to
 * load unknown type signatures.  It maintains a mapping from fully
 * qualified names to the CClass instances representing their
 * signatures.  Specifically the mapping is from a fully qualified
 * type name to a set of instances that can be sorted.  In MultiJava
 * that set is a singleton set; however, for tools like JML where a
 * single fully qualified name can refer to a specification and one or
 * more refinements to that specification, the set may contain
 * multiple items.  
 */
public class JmlTypeLoader extends TypeLoader {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    public static JmlTypeLoader getJmlSingleton() {
	if (singletonInstance == null) {
	    singletonInstance = new JmlTypeLoader();
	}
	return singletonInstance;
    }

    private JmlTypeLoader() {
	this(new JmlFileFinder());
    }

    /** Creates an instance with the given file finder. This
     * constructor is for use by subclass. */
    protected JmlTypeLoader(JmlFileFinder finder) {
	super(finder);
    }

    // ----------------------------------------------------------------------
    // CLASS LOADING METHODS
    // ----------------------------------------------------------------------

    /**
     * Empties the compilation session caches to prepare for a new
     * compilation session.
     */
    public void initSession( ) {
	fileASTs.clear();	// must come before super call so ASTs of types
				// loaded by superclass are cached
        typeDeclASTs.clear();
	super.initSession();
	JmlStdType.initSession();
	filesProcessed.clear();
	incompleteTasksByQName.clear();
    }

    /**
     * Adds the given source class to the table of available classes. 
     * Returns true if the class was not declared in more than one 
     * source file and false otherwise.
     *
     * <pre><jml>
     * also
     *   requires typ != null;
     *   modifies compilationSessionTypeCache, filesProcessed;
     * </jml></pre>
     */
    public boolean addToTypeCache( CClass typ ) {
	boolean isUnique = super.addToTypeCache( typ );
	if (typ instanceof JmlSourceClass) {
	    loadMostRefinedType((JmlSourceClass) typ);
	}
	return isUnique;
    }

    /**
     * Look for partially processed compilation unit (if suspended) for the 
     * qualified type name <code>qName</code>.
     */
    public JmlCompilationUnit getSuspendedCUnit(String qName) {
	int pos = qName.indexOf('$');
	JmlCompilationUnit cUnit;
	if (pos < 0) {
	    cUnit = (JmlCompilationUnit) incompleteTasksByQName.get(qName);
	} else {
	    cUnit = (JmlCompilationUnit) 
		incompleteTasksByQName.get(qName.substring(0, pos));
	}
	return cUnit;
    }

    /**
     * Reactivate the task for the qualified type name <code>qName</code>.
     */
    public void activateSymbolTableBuild(String qName) {
	JmlCompilationUnit cUnit = getSuspendedCUnit(qName);
	if ( cUnit != null ) {
	    activateSymbolTableBuild( cUnit );
	}
    }

    /**
     * Reactivate the task for the compilation unit <code>cUnit</code>
     * if the symbol table has not been built.
     */
    public void activateSymbolTableBuild( JmlCompilationUnit cUnit) {
	if ( !cUnit.isSymbolTableFinished() ) {
	    activatePartiallyProcessedTask( cUnit );
	}
    }

    /**
     * Reactivate the task for the qualified type name <code>qName</code>.
     */
    public void activateTypeCheck(String qName) {
	JmlCompilationUnit cUnit = getSuspendedCUnit(qName);
	if ( cUnit != null ) {
	    activateTypeCheck( cUnit );
	}
    }

    /**
     * Reactivate the task for the compilation unit <code>cUnit</code>
     * if the symbol table has not been built.
     */
    public void activateTypeCheck( JmlCompilationUnit cUnit) {
	if ( !cUnit.isTypeCheckFinished() ) {
	    activatePartiallyProcessedTask( cUnit );
	}
    }

    /**
     * Reactivate the task for the compilation unit <code>cUnit</code>.
     */
    public void activatePartiallyProcessedTask( JmlCompilationUnit cUnit ) {
	Task task = cUnit.getSuspendedTask();
	if (task != null) {
	    Main compiler = (Main) CTopLevel.getCompiler();
	    removePartiallyProcessedTask(cUnit);
	    // System.out.println("reactivate:"+cUnit.getFilePath());
	    compiler.catchUpTask(task);
	}
    }

    /**
     * Save the task in case it needs to be reactivated.
     */
    public void savePartiallyProcessedTask( JmlCompilationUnit cUnit ) {
	// System.out.println("save:"+cUnit.getFilePath());
	JTypeDeclarationType[] types = cUnit.typeDeclarations();
	for( int j = 0; j < types.length; j++ ) {
	    if( types[j] instanceof JmlTypeDeclaration ) {
		JmlTypeDeclaration typeDecl = (JmlTypeDeclaration)types[j];
		String qName = typeDecl.getCClass().qualifiedName();
		incompleteTasksByQName.put(qName, cUnit);
	    }
	}
    }

    public void removePartiallyProcessedTask( JmlCompilationUnit cUnit ) {
	JTypeDeclarationType[] types = cUnit.typeDeclarations();
	for( int j = 0; j < types.length; j++ ) {
	    if( types[j] instanceof JmlTypeDeclaration ) {
		JmlTypeDeclaration typeDecl = (JmlTypeDeclaration)types[j];
		String qName = typeDecl.getCClass().qualifiedName();
		incompleteTasksByQName.remove(qName);
	    }
	}
	cUnit.setSuspendedTask(null);
    }

    /**
     * Returns true if typ is a legal unique type declaration.
     * @param typ  a type to be added to the cache
     * @param last the previous cache entry mapped to by typ.qualifiedName()
     */
    protected /*@ pure @*/ boolean checkUniqueness(CClass typ, CClass last) {
	return (last == null);
    }

    /**
     * Called by Main when the given file, from which the given
     * compilation unit AST was derived, did not contain an expected
     * result; this method removes all cached info. for the file.
     */
    protected void forgetEverythingAbout(File f, JCompilationUnitType cunit) {
	super.forgetEverythingAbout(f,cunit);
	filesProcessed.remove(f);
    }

    /**
     * Removes the qualified name of the given source class from 
     * the table of loaded classes (so it can be reloaded without 
     * causing conflicts). This is only done if the conflict 
     * occurs because the names were added during two different 
     * compilation sessions.
     *
     * <pre><jml>
     *  also
     *    requires typ != null;
     *    modifies compilationSessionTypeCache, vmSessionTypeCache,
     *             filesProcessed;
     * </jml></pre>
     */
    protected void removeFromTypeCache( CClass typ ) {
	if ( typ instanceof JmlSourceClass ) {
	    JmlSourceClass currType = ((JmlSourceClass)typ).getMostRefined();
	    filesProcessed.remove( getFilePath(currType.sourceFile()) );
	    // System.out.println("removing "
	    // 		          + getFilePath(currType.sourceFile()));
	}
	super.removeFromTypeCache(typ);
	typeDeclASTs.remove(typ);
    }

    /**
     * Records the host class nearest to the current context which is 
     * used by the method <code>reloadType</code>.
     * This is needed so typechecking of refinement chains are 
     * handled properly.  
     */
    public static void setCurrentHostClass(CClass sourceClass) {
	currentHostClass = sourceClass;
    }

    /**
     * Returns the nearest host class to the current context. 
     */
    public static CClass getCurrentHostClass() {
	return currentHostClass;
    }

    /**
     * <pre><jml>
     *  also
     *    requires sourceClass != null;
     * </jml></pre>
     */
    public CClass reloadType(CClass sourceClass) {
	if (sourceClass instanceof JmlSourceClass) {
	    if (currentHostClass instanceof JmlSourceClass) {
		if ( currentHostClass.qualifiedName()
		     .equals(sourceClass.qualifiedName()) ) {
		    return currentHostClass;
		} 
	    }
	    return ((JmlSourceClass)sourceClass).getMostRefined();
	} else {
	    return sourceClass;
	}
    }

    /**
     * Loads the "most refined" source class of this type.
     *
     * <pre><jml>
     *    requires sourceClass != null;
     *    modifies compilationSessionTypeCache, vmSessionTypeCache,
     *             filesProcessed;
     * </jml></pre>
     */
    protected final void loadMostRefinedType(JmlSourceClass sourceClass) {
	String qName = sourceClass.qualifiedName();
	String sourceFileIdent = getFileIdent(sourceClass.sourceFile());
	if (! sourceClass.ident().equals(sourceFileIdent)) {
	    // The file name and class name do not match.
	    // Therefore, the class defined cannot be public 
	    // and cannot be refined.
	    return;
	}

	ClassPath.ClassDescription desc = findSourceFile(qName);
	if (desc != null) {
	    File mostRefinedFile = 
		((ClassPath.FileClassDescription)desc).file();
	    Main compiler = (Main) sourceClass.getCompiler();
	    if (! compiler.isCommandLineFile(mostRefinedFile)) {
		// Only need to catch up if NOT already listed on 
		// the command line
		String key = getFilePath(mostRefinedFile);
		JmlSourceClass mayBeMostRefined = 
		    ((JmlSourceClass)sourceClass).getMostRefined();
		filesProcessed.add( 
		    getFilePath(mayBeMostRefined.sourceFile()) );

		// System.out.println("adding " 
		// + getFilePath(mayBeMostRefined.sourceFile()) 
		// + "\n    " + mayBeMostRefined.getCompiler());
		if ( ! filesProcessed.contains(key) ) {
		    // System.out.print("catchUp "
		    //		 + mayBeMostRefined.sourceFile().getName());
		    // System.out.println(" to " + mostRefinedFile.getName());
		    compiler.catchUpType(mostRefinedFile, qName);
		    filesProcessed.add(key);
		}
	    }
	}
    }

    /**
     * Returns the Java identifier associated with the name of the
     * file contained in this file.  For example, if the
     * file is named &quot;MyClass.java&quot; then this method
     * returns &quot;MyClass&quot;.
     */
    protected /*@ pure @*/ String getFileIdent(File f) {
	String baseName = f.getName();
	String fileIdent;
	int pos = baseName.indexOf( "." );
	if( pos < 0 ) {
	    fileIdent =  baseName;
	} else {
	    fileIdent = baseName.substring( 0, pos );
	}
	return fileIdent;
    }

    /**
     * Determines whether the given Class, using its fully qualified name, 
     * has been declared in more than one file. 
     * This method is needed by JML in order to handle classes that 
     * have been refined, e.g., when its specifications have intentionally 
     * been declared in a separate file.
     *
     * Returns true if the class has been declared in more than 
     * one source file (unless refined), and false otherwise.
     *
     * <pre><jml>
     *  also
     *    requires clazz != null; 
     * </jml></pre>
     *
     */
    public boolean isDeclaredInDifferentSourceFiles( boolean isUnique, 
						     CClass clazz ) {
	if (isUnique) {
	    return false;
	}
	if ( clazz.isNestedType() ) {
	    // this error is detected elsewhere!
	    return false;
	}
	String qName = clazz.qualifiedName();
	
	CClass typ = 
	    (CClass) MjcHashRelation.getNextValueFromN( 
		new MjcHashRelation[] { compilationSessionTypeCache,
					vmSessionTypeCache },
		qName, clazz );
	if ( typ != clazz ) {
	    if (  (typ instanceof CSourceClass) 
		  && clazz.compareTo(typ) == 0
		  && clazz.sourceFile() != typ.sourceFile() ) {
		return true;
	    }
	}
	return false;
    }

    // -------------------------------------------------------------
    // ABSTRACT SYNTAX TREE CACHES
    // -------------------------------------------------------------

    /**
     * Records a mapping from the given file to the given AST.
     */
    public final JCompilationUnitType putCUnitAST(File f,
                                                  JCompilationUnitType cunit)
    {
	String key = getFilePath(f);
	if (cunit != null) {
	    return (JCompilationUnitType) fileASTs.put(key, cunit);
	}
	return null;
    }


    /**
     * Returns the AST parsed from the given file, or null if no AST
     * is cached for the given file (either because the file has not
     * been parsed or because no AST was created when parsing the
     * file.
     */
    public final JCompilationUnitType getCUnitAST(File f) {
	String key = getFilePath(f);
	return (JCompilationUnitType) fileASTs.get(key);
    }    

    /**
     * Adds a JML type declaration into the database.
     * The type declaration is assumed to have been interface-checked 
     * with its signature added to the signature forest, i.e., 
     * <code>typeDecl.getCClass() != null</code>.
     * 
     * <pre><jml>
     * requires decl != null && decl.getCClass() != null &&
     *   !typeDeclASTs.containsKey(decl);
     * </jml></pre>
     */
    public final void addTypeDeclAST(JmlTypeDeclaration decl) {
	CClass cls = decl.getCClass();
	typeDeclASTs.put(cls, decl);
    }

    /**
     * Returns the JML type declaration corresponding to the given source
     * class; <code>null</code> is returned if no corresponding JML type
     * declaration is found in the database.
     *
     * <pre><jml>
     * requires typ != null;
     * </jml></pre>
     */
    public final JmlTypeDeclaration typeDeclarationOf(CClass typ) {
	return (JmlTypeDeclaration)typeDeclASTs.get(typ);
    }

    /**
     * Returns the refined declaration of a given JML class declaration. 
     * If the given class is not a refining declaration, 
     * <code>null</code> is returned.
     *
     * <pre><jml>
     * requires cdecl != null && cdecl.getCClass() != null;
     * </jml></pre>
     */
    public final JmlTypeDeclaration refinedDeclOf(JmlTypeDeclaration cdecl) 
    {
	JmlSourceClass declSrc = (JmlSourceClass) cdecl.getCClass();
	declSrc = declSrc.getRefinedType();
	if (declSrc != null) {
	    return typeDeclarationOf(declSrc);
	} else {
	    return null;
	}
    }

    /**
     * Returns the superclass of a given JML class declaration. If the given
     * class has no superclass or its superclass is a binary class (i.e., not
     * registered in the database), <code>null</code> is returned.
     *
     * <pre><jml>
     * requires cdecl != null && cdecl.getCClass() != null;
     * </jml></pre>
     */
    public final JmlClassDeclaration superClassOf(JmlClassDeclaration cdecl) 
    {
	return superClassOf(cdecl.getCClass());
    }

    /**
     * Returns the superclass of a given JML class declaration. If the class
     * has no superclass or its superclass is a binary class (i.e., not
     * registered in the database), <code>null</code> is returned.
     *
     * <pre><jml>
     * requires cls != null;
     * </jml></pre>
     */
    public final JmlClassDeclaration superClassOf(CClass cls)
    {
	CClass sc = cls.getSuperClass();
	return (JmlClassDeclaration) typeDeclarationOf(sc);	
    }

    /**
     * Returns the interfaces of a given JML type declaration. If the given
     * type has no interface or all of its interfaces are binaries (i.e., not
     * registered in the database), an empty array is returned.
     * Binary interfaces, i.e., interfaces parsed from bytecode are
     * omitted from the return array.
     *
     * <pre><jml>
     * requires typeDecl != null && typeDecl.getCClass() != null;
     * </jml></pre>
     */
    public final JmlInterfaceDeclaration[] interfacesOf(JmlTypeDeclaration typeDecl)
    {
	CClassType[] ctypes = typeDecl.interfaces();
	ArrayList tdecls = new ArrayList();
	for (int i = 0; i < ctypes.length; i++) {
	    Object td = typeDeclarationOf(ctypes[i].getCClass());
	    JmlInterfaceDeclaration tdecl = (JmlInterfaceDeclaration) td;
	    if (tdecl != null) {
		tdecls.add(tdecl);
	    }
	}
	return (JmlInterfaceDeclaration[])
	    tdecls.toArray(new JmlInterfaceDeclaration[tdecls.size()]);
    }
    
    // -------------------------------------------------------------
    // VIRTUAL MACHINE SESSION CACHE MANAGEMENT
    // -------------------------------------------------------------

    /**
     * Returns true if the information for the type or package of the
     * given qualified name should be retained for subsequent
     * compilation sessions.
     *
     * <pre><jml>
     * also
     *  requires qName != null && (* package separators in qName are '/' not '.' *);
     * </jml></pre>
     */
    protected /*@ spec_public pure @*/ boolean isTrusted( String qName ) {
	//return false;
   	return super.isTrusted(qName) 
            || qName.startsWith("org/jmlspecs/models");
    }

    /**
     * Creates and returns a class info object by reading the symbol
     * file for the class with the given fully qualified name
     * <code>qName</code>.  If no symbol file is found, null is
     * returned. This method also creates a binary class object and
     * adds it to the system cache. This method is overriden here to
     * create JML-specific class info object and binary class object.
     */
    protected ClassInfo createClassInfo(String qName) {
	// first, read from .sym file
	ClassInfo info;
	try {
	    info = org.multijava.util.classfile.ClassPath.getClassInfo(
		qName, 
		JmlFileFinder.SYMBOL_SUFFIX, 
		JmlClassInfoCreator.getInstance(),
		false,
		true);
	} catch (ClassFileReadException e) {
	    CTopLevel.getCompiler().reportTrouble(e);
	    info = null;
	}
	if (info != null) {
	    new JmlSigBinaryClass(CTopLevel.getFromClassesCompiler(), 
				  info);
	} else {
	    // read from .class file
	    info = super.createClassInfo(qName);
	}
	return info;
    }

    // ---------------------------------------------------------------------- 
    // PRIVILEGED DATA MEMBERS
    // ----------------------------------------------------------------------

    /*@ spec_public @*/ private static HashSet filesProcessed = new HashSet();

    /**
     * A mapping from files to the ASTs parsed from those files.  Note
     * that the domain of this map is not necessarily equal to the
     * filesProcessed set.
     */
    private HashMap fileASTs = new HashMap();

    private HashMap incompleteTasksByQName = new HashMap();

    /** A mapping from <code>CClass</code> to <code>JmlTypeDeclaration</code> 
     * for traversal of "extends" and "implements" hierarchies.
     *
     * <pre><jml>
     * invariant typeDeclASTs != null;
     * </jml></pre>
     */
    private /*@ spec_public @*/ static HashMap typeDeclASTs = new HashMap();

    private static CClass currentHostClass = null;

    private static JmlTypeLoader singletonInstance;
}
