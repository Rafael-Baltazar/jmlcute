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
 * $Id: JmlTypeDeclaration.java,v 1.103 2007/02/08 14:05:49 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CField;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.CompilerPassEnterable;
import org.multijava.mjc.JConstructorDeclarationType;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JMemberDeclarationType;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JTypeDeclaration;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcMessages;
import org.multijava.util.Utils;
import org.multijava.util.compiler.CWarning;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This type represents a java class or interface in the syntax tree.
 */
public abstract class JmlTypeDeclaration extends JmlMemberDeclaration 
    implements JTypeDeclarationType 
{
    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------
    
    public JmlTypeDeclaration( /*@ non_null */ TokenReference where, 
			       /*@ non_null */  boolean[] interfaceWeaklyFlags,
			       /*@ non_null */ JmlInvariant[] invariants,
			       /*@ non_null */ JmlConstraint[] constraints,
			       /*@ non_null */ JmlRepresentsDecl[] representsDecls,
			       /*@ non_null */ JmlAxiom[] axioms,
			       /*@ non_null */ JmlVarAssertion[] varAssertions,
			       /*@ non_null */ JTypeDeclaration delegee ) 
    {
	super( where, delegee );
	this.interfaceWeaklyFlags = interfaceWeaklyFlags;
	this.invariants = invariants;
	this.constraints = constraints;
	this.representsDecls = representsDecls;
	this.axioms = axioms;
	this.varAssertions = varAssertions;
	this.delegee = delegee;	// a local reference avoids casts
    }
    
    /**
     * Generates a <code>CSourceClass</code> class signature singleton
     * for this declaration.
     *
     * @param compiler	the compiler instance for which this singleton is 
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
    public void generateInterface( org.multijava.mjc.Main compiler, CClass owner, 
				   CMemberHost host, String prefix, 
				   boolean isAnon, boolean isMember )
    {
	delegee.generateInterface( compiler, owner, host, prefix, isAnon, 
				   isMember );

	// add the AST for this type declaration to the cache
	JmlTypeLoader.getJmlSingleton().addTypeDeclAST(this);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    public /*@ pure @*/ boolean[] interfaceWeaklyFlags() {
	return interfaceWeaklyFlags;
    }

    public /*@ pure @*/ JmlInvariant[] invariants() {
	return invariants;
    }

    public /*@ pure @*/ JmlConstraint[] constraints() {
	return constraints;
    }

    public /*@ pure @*/ JmlRepresentsDecl[] representsDecls() {
	return representsDecls;
    }

    public /*@ pure @*/ JmlAxiom[] axioms() {
	return axioms;
    }

    public /*@ pure @*/ JmlVarAssertion[] varAssertions() {
	return varAssertions;
    }

    public /*@ pure @*/ JmlInvariant[] combinedInvariants() {
	return combinedInvariants;
    }

    public /*@ pure @*/ JmlConstraint[] combinedConstraints() {
	return combinedConstraints;
    }

    public /*@ pure @*/ JmlRepresentsDecl[] combinedRepresentsDecls() {
	return combinedRepresentsDecls;
    }

    public /*@ pure @*/ JmlAxiom[] combinedAxioms() {
	return combinedAxioms;
    }

    public /*@ pure @*/ JmlVarAssertion[] combinedVarAssertions() {
	return combinedVarAssertions;
    }

    public /*@ pure @*/ CTypeVariable[] typevariables()
    {
    return delegee.typevariables();
    }

    public /*@ pure @*/ CClassType[] interfaces()
    {
	return delegee.interfaces();
    }

    /**
     * Returns an array of the static and instance initializers for
     * the type represented by this.  */
    public /*@ pure @*/ JPhylum[] fieldsAndInits()
    {
	return delegee.fieldsAndInits();
    }

    public /*@ pure @*/ ArrayList methods()
    {
	return delegee.methods();
    }

    public void setMethods(ArrayList m) {
	delegee.setMethods(m);
    }

    public /*@ pure @*/ ArrayList inners()
    {
	return delegee.inners();
    }
    
    public void setInners(ArrayList v) {
	delegee.setInners(v);
    }

    /**
     * @return	true if this class is at top level
     */
    public /*@ pure @*/ boolean isAtTopLevel()
    {
	return delegee.isAtTopLevel();
    }

    public /*@ pure @*/ JFieldDeclarationType[] fields()
    {
	return delegee.fields();
    }

    public /*@ pure @*/ JConstructorDeclarationType getDefaultConstructor()
    {
	return delegee.getDefaultConstructor();
    }

    public void setDefaultConstructor( JConstructorDeclarationType defaultConstructor)
    {
	delegee.setDefaultConstructor( defaultConstructor );
    }

    public void setIdent(String ident)
    {
        System.out.println("----- DEBUG: pre: " + ident);
	delegee.setIdent( ident);
        System.out.println("----- DEBUG: post: " + delegee.ident());
        System.out.println("----- DEBUG: post: " + delegee.getClass());
    }

    /**
     * Returns the identifier for this type declaration.
     * @return	the unqualified identifier for this type declaration
     */
    public /*@ pure @*/ String ident()
    {
	return delegee.ident();
    }

    /**
     * Adds the given member to this type's interface and modifies 
     * sourceClass to include the new member
     *
     * @param	newMember	a member to be added to this type
     */
    public void addMember( JMemberDeclarationType newMember )
    {
	delegee.addMember(  newMember );
    }

    public void setFields( JPhylum[] fields ) {
	delegee.setFields( fields );
    }

    public void setFieldsOnly( JFieldDeclarationType[] fields ) {
	delegee.setFieldsOnly( fields );
    }

    /**
     * Returns the logical owner of this type.  */
    public /*@ pure @*/ CClass owner()
    {
	return delegee.owner();
    }

    public /*@ pure @*/ long modifiers()
    {
	return delegee.modifiers();
    }

    /**
     * Marks this type as static.
     *
     * <pre><jml>
     * also
     *   requires (* this.generateInterface(...) has not been invoked *);
     *   requires_redundantly (* sourceClass == null *); 
     *   ensures hasFlag(delegee.modifiers(), ACC_STATIC);
     * </jml></pre>
     *
     */
    public void setStatic() {
	delegee.setStatic();
    }
    

    /**
     * Marks this type as non-static.
     *
     * <pre><jml>
     * also 
     * ensures !hasFlag(delegee.modifiers,ACC_STATIC);
     * </jml></pre>
     */
    public void unsetStatic() {
	delegee.unsetStatic();
    }

 	/**
	 * Records the fact that even though the class is an inner
	 * class, we should not generate an outer this for it, because
	 * the outer this is not accessible.
	 * The sourceClass field should not be null.
	 */
    public void syntheticOuterThisInaccessible() {
	delegee.syntheticOuterThisInaccessible();
    }

    
    /**
     * Adds the signature CSourceClass of this, and of all nested
     * types, to accum.
     */
    public void accumAllTypeSignatures(ArrayList accum) {
	delegee.accumAllTypeSignatures(accum);
    }

    /**
     * Returns true if this type declaration is for a final type. */
    public /*@ pure @*/  boolean isFinal() {
        return hasFlag(modifiers(), ACC_FINAL);
    }

    /**
     * Returns true if this is a class declaration. */
    public abstract /*@ pure @*/ boolean isClass();

    /**
     * Returns true if this is an interface declaration. */
    public /*@ pure @*/ boolean isInterface() {
        return !isClass();
    }

    /**
     * Returns true if this type declaration has a source file in the
     * refinement chain. This method is used by jmlrac. */
    public /*@ pure @*/ boolean hasSourceInRefinement() {
        return hasSourceInRefinement;
    }

    /**
     * Sets that if this type declaration has a source file in the
     * refinement chain. This method is used by jmlrac. */
    public void setHasSourceInRefinement(boolean flag) {
        hasSourceInRefinement = flag;
    }

    /**
     * @return	the member access information object for this member.
     */
    public /*@ non_null @*/ JmlMemberAccess jmlAccess() {
	if (jmlAccess == null) {
	    JmlSourceClass self = (JmlSourceClass) delegee.getCClass();
	    jmlAccess = self.jmlAccess();
	}
	return jmlAccess;
    }

    /**
     * Returns true if this member is declared in a '.java' file.
     */
    public boolean inJavaFile() {
	// This method override is necessary because the 
	// owner of this type is not necessarily a class 
	// so the super class method will not work!!!
	// (see method inJavaFile() of JmlMemberAccess); 
	return ((JmlSourceClass)getCClass()).inJavaFile();
    }
    
    // ----------------------------------------------------------------------
    // QUICK ACCESSORS
    // ----------------------------------------------------------------------


    /**
     * Computes the data group map (if it has not already been computed) 
     * and returns it.  The data group map is a map from each field to the 
     * set of fields in its data group.  Only model, spec_public, 
     * and spec_protected fields can have more than one field (itself) 
     * in this set.
     */
    public JmlDataGroupMemberMap getDataGroupMap() {
	initializeDataGroupMap();
	return dataGroupMap;
    }

    /**
     * Computes and stores the model fields of this type into an array.
     * These are the fields that need to have a represents clause 
     * and have an associated data group.   
     *
     * Returns an array of the model fields of this type 
     * (not including model fields inherited from interfaces 
     * implemented or from the superclass).
     */
    public JFieldDeclarationType[] getModelFields() {
	if (modelFields != null) {
	    // the model fields have already been computed
	    return modelFields;
	}
	combineSpecifications();

	ArrayList modelAccum = new ArrayList(combinedFields.length);
	for (int i=0; i<combinedFields.length; i++) {
	    JmlFieldDeclaration nextField 
		= (JmlFieldDeclaration) combinedFields[i];
	    if ( nextField.isModel() ) {
		modelAccum.add(nextField);
	    }
	}

	// cache the model fields of this type 
	modelFields = new JFieldDeclarationType[modelAccum.size()];
	modelAccum.toArray(modelFields);
	
	return modelFields;
    }

    /**
     * Initializes the map from <code>JmlSourceField</code>, a data group,  
     * to a <code>JmlAssignableFieldSet</code>, the set of fields 
     * in that data group.  
     */
    protected void initializeDataGroupMap() {
	if (this.dataGroupMap != null) {
	    // the map has already been computed
	    return;
	}
	combineSpecifications();
	// accumulate the model fields in this type declaration
	this.dataGroupMap = new JmlDataGroupMemberMap();

	for (int i=0; i<combinedFields.length; i++) {
	    JmlFieldDeclaration nextField 
		= (JmlFieldDeclaration) combinedFields[i];
	    dataGroupMap.addGroup( (JmlSourceField)nextField.getField() );
	}

	// Merge with inherited data group map
	if (this instanceof JmlClassDeclaration) {
	    JmlClassDeclaration superType 
		= JmlTypeLoader.getJmlSingleton()
		.superClassOf((JmlClassDeclaration)this);
	    if (superType != null) {
		JmlDataGroupMemberMap superMap = superType.getDataGroupMap();
		dataGroupMap.addInheritedMembers( superMap );
	    }
	}

	// add new members to the data group map
	for (int i=0; i<combinedFields.length; i++) {
	    JmlFieldDeclaration nextField 
		= (JmlFieldDeclaration) combinedFields[i];
	    nextField.addToDataGroups( dataGroupMap );
	}
	// System.out.println("map for type "+ident()+"\n"+dataGroupMap);
    }

    /** 
     * Returns all model fields inherited from abstract superclasses.
     * This method must be called at the end of typechecking.
     */
    public JFieldDeclarationType[] getAllSuperClassModelFields()
    {
	if (superClassModelFields != null) {
	    // return the cached array
	    return superClassModelFields;
	}
	Set s = new HashSet();
	JmlClassDeclaration superType 
	    = JmlTypeLoader.getJmlSingleton()
	    .superClassOf((JmlClassDeclaration)this);
	while (superType != null && superType.jmlAccess().isAbstract() ) {
	   s.addAll(Arrays.asList(superType.getModelFields()));
	   superType = JmlTypeLoader.getJmlSingleton()
	       .superClassOf(superType);
	}

	// cache the model fields inherited from the super class 
	superClassModelFields = new JFieldDeclarationType[s.size()];
	s.toArray( superClassModelFields );
	return superClassModelFields;
    }

    /** 
     * Returns all model fields inherited through the interface hierarchy.
     * This method must be called at the end of typechecking.
     */
    public JFieldDeclarationType[] getAllInterfaceModelFields()
    {
	if (interfaceModelFields != null) {
	    // return the cached array
	    return interfaceModelFields;
	}
	HashSet s = new HashSet();
	JmlInterfaceDeclaration[] interfaces  
	    = JmlTypeLoader.getJmlSingleton().interfacesOf(this);
	for (int i = 0; i < interfaces.length; i++) {
	    s.addAll(Arrays.asList(interfaces[i].getAllInterfaceModelFields()));
	}

	// cache the model fields inherited from interfaces
	interfaceModelFields = new JFieldDeclarationType[s.size()];
	s.toArray( interfaceModelFields );
	return interfaceModelFields;
    }

    /**
     * Finds the applicable <code>represents</code>clause for a given
     * model field by searching through the superclass and interface
     * hierachies starting from the given type declaration.  If such a
     * clause is found, returns the type declaration that includes the
     * clause; otherwise, returns <code>null</code>.
     *
     * <pre><jml>
     * requires field != null && hasFlag(field.modifiers(),ACC_MODEL);
     * ensures \result != null ==> (* \result has represents clause  r 
     *   such that !r.isRedundantly() && r.usesAbstractionFunction() && 
     *   r.storeRef() refers to field *);
     * </jml></pre>
     */
    public JmlTypeDeclaration findTypeWithRepresentsFor(CField field)
    {
	// First search for an applicable represents clause in this decl.
	JmlRepresentsDecl[] rdecls = this.representsDecls();
	JmlRepresentsDecl redundantRep = null;
	if (rdecls != null) {
	    for (int i = 0; i < rdecls.length; i++) {
                try { 
                    JmlSourceField repField = rdecls[i].getField();
                    if ( field == repField ) {
			if ( !rdecls[i].isRedundantly() ) {
			    // skip redundant represents clause
			    return this;
			} else {
			    redundantRep = rdecls[i];
			}
		    } else if ( repField == null ) { 
			if ( field.ident().equals(rdecls[i].ident()) ) {
			    return this;
			}
		    }
                } catch (NullPointerException e) {
                    // If this Type decl is not type checked (e.g., recursively
                    // included type), the getField method call throws
                    // a NullPointerException.
                    // !FIXME! Need to consider field hiding.
                    if (field.ident().equals(rdecls[i].ident())) {
                        return this;
		    }
                }
	    }
	}

	// continue the search through the refinement chain
	JmlTypeDeclaration result = null;
	JmlTypeDeclaration refinedDecl 
	    = JmlTypeLoader.getJmlSingleton().refinedDeclOf(this);
	if (refinedDecl != null) {
	    result = refinedDecl.findTypeWithRepresentsFor( field );
	    if (result != null) {
		return result;
	    }
	}

	// continue the search through the non-static inner classes
	ArrayList inners = inners();
	Iterator iter = inners.iterator();
	while (iter.hasNext()) {
	    JmlTypeDeclaration innerType = (JmlTypeDeclaration) iter.next();
	    result = innerType.findTypeWithRepresentsFor( field );
	    if (result != null) {
		return result;
	    }
	}

	// if the model field is declared inside this, then there is 
	// no need to continue the search up through superclasses
        // and interfaces
	CClass fieldOwner = field.owner();
	CClass selfSrc = this.getCClass();
	if (fieldOwner == selfSrc) {
	    result = checkRedundantRepresents( redundantRep, field.ident() );
	    return result;
	}

	// continue the search through the superclass hierarchy
	if (this instanceof JmlClassDeclaration) {
	    JmlClassDeclaration superDecl 
		= JmlTypeLoader.getJmlSingleton()
		.superClassOf((JmlClassDeclaration)this);
	    if (superDecl != null) {
		result = superDecl.findTypeWithRepresentsFor(field);
		if (result != null) {
		    return result;
		}
	    }
	}

	// finally, continue the search through the interfaces
	JmlInterfaceDeclaration[] interfaces 
	    = JmlTypeLoader.getJmlSingleton().interfacesOf(this);
	for (int i = 0; i < interfaces.length; i++) {
	    JmlTypeDeclaration idecl 
		= interfaces[i].findTypeWithRepresentsFor( field );
	    if (idecl != null) {
		return idecl;
	    }
	}
	result = checkRedundantRepresents( redundantRep, field.ident() );
	return result;
    }

    private JmlTypeDeclaration 
	checkRedundantRepresents( JmlRepresentsDecl redundantRep,
				  String ident ) 
    {
	if (redundantRep != null) {
	    // represents_redundantly but no represents clause
	    CTopLevel.getCompiler().reportTrouble(
		    new PositionedError( redundantRep.getTokenReference(),
					 JmlMessages.REDUNDANT_REPRESENTS,
					 ident )
		    );
	    return this;
	}
	return null; // no such type declaration found
    }

    /**
     * Walks up the extends hierarchy and adds all methods
     * to the returned ArrayList.
     *
     * @return		a ArrayList that includes the CMethods for all 
     *			methods in this class and all direct ancestors
     */
    //@ pure
    public ArrayList getAllMethods() {
	return delegee.getAllMethods();
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Performs preliminary processing on compilation units and types.
     * Processes type imports so external methods' receiver types can
     * be analyzed and supertypes can be resolved.  Groups external
     * methods by name, corresponding to the anchor classes that will
     * eventually be generated.  Mutates the name space management in
     * CTopLevel to record a CGenericFunctionCollection singleton for
     * each anchor class.  */
    public void preprocessDependencies( CContextType context ) 
	throws PositionedError 
    {
	delegee.preprocessDependencies( context );

	// must be done before linking inner types in the next pass
	JmlSourceClass selfSrc = (JmlSourceClass) delegee.getCClass();
	selfSrc.setAST(this);
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
     *
     * @param		context		the context in which this
     *					decl appears
     * @exception	PositionedError	an error with reference to 
     *					the source file
     */
    public void checkInterface( CContextType context ) throws PositionedError {

	// Link the types in a refinement chain together.
	// Link them before checking the interface so they are 
	// linked before they are checked. 
	linkInnerTypeRefinements();

        // Peform JML interface check relative to spec scope because
        // some type names (e.g., model, spec_public) are visible
        // only in spec scope depending on the modifiers of this type.

        final long modifiers = modifiers();
	try {
	    enterSpecScope(modifiers);
            delegee.checkInterface( context );
	}
	finally {
	    exitSpecScope(modifiers);
	}            

	JmlSourceClass selfSrc = (JmlSourceClass) delegee.getCClass();
	// don't make this check if it's an inner type
	if (context.findNearestHost() instanceof CCompilationUnit) {
	    try {
		JmlSourceClass refinedSrcType = selfSrc.getRefinedType();
		selfSrc.checkFileNameAndSuffix(refinedSrcType);
	    } catch (UnpositionedError e) {
		throw new PositionedError( getTokenReference(),
					   e.getFormattedMessage());
	    }
	}
    }

    /**
     * Checks the static initializers created during the
     * checkInterface pass and performs some other checks that can be
     * performed simply before full blown typechecking.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if check fails */
    public void checkInitializers(CContextType context) throws PositionedError
    {
	delegee.checkInitializers( context );

	// Refining methods and fields in a refinement chain must 
	// be linked together before type checking!
	// To handle data group inheritance, even types that are not 
	// going to be type checked have to be properly linked 
	// before the type checking pass.
	// The two methods that follow cannot be called until after 
	// the symbol table has been built by the previous phases 
	// because they lookup fields and methods in type signatures  
	// to make the links.  The type signatures were linked 
	// during the two previous passes (i.e., preprocessDependencies 
	// and checkInterface).  

	linkFieldRefinements();
	linkMethodRefinements();
	CClass clazz = delegee.getCClass();
	if (clazz instanceof JmlSourceClass) {
	    ((JmlSourceClass)clazz).setFinishedPreProcessing();
	}
    }

    /**
     * Computes the values of specializer expressions used to dispatch on
     * compile-time constants.
     * The JML-specific combining of specifications is done 
     * during this pass so computing the data group members and 
     * the assignable fields of a method can be computed during 
     * typechecking.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if the check fails */
    public abstract void resolveSpecializers(/*@non_null*/ CContextType context)
	throws PositionedError;

    
    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Finds the top method of every declared method.  Called after
     * the checkInitializers pass.  This cannot be done before then
     * because the external generic function mappings are not complete
     * until the end of the checkInterface pass and the constant value
     * specializers are not known until after the checkInitializers
     * pass.  This must be done before the typecheck pass so that all
     * specialized argument positions for generic functions are known
     * for ambiguity checking. */
    public void resolveTopMethods() throws PositionedError {
	delegee.resolveTopMethods();
    }

    /**
     * Typechecks this type declaration in the context in which it
     * appears.  Mutates the context to record the information learned
     * during checking.  Actually just updates the context by adding a
     * CSourceClass representation of this.  Overriding methods in
     * subclasses of this handle the actual checks.
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CContextType context ) throws PositionedError
    {

	final long modifiers = modifiers();

	//by default, the arithmetic types are:
	//ACC_CODE_JAVA_MATH and ACC_SPEC_JAVA_MATH

	//to avoid too much function calls, here is a local copy of some of
	//the booleans used to perform checking
	boolean code_java_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_JAVA_MATH);
	boolean code_safe_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_SAFE_MATH);
	boolean code_bigint_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_BIGINT_MATH);
	boolean code_default 
	    = !(code_java_math||code_safe_math||code_bigint_math);
	boolean spec_java_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_JAVA_MATH);
	boolean spec_safe_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_SAFE_MATH);
	boolean spec_bigint_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_BIGINT_MATH);
	boolean spec_default 
	    = !(spec_java_math||spec_safe_math||spec_bigint_math);

	//make sure that there are no conflictual arithmetic mode flags
	if(!code_default)
	{
		check(context,
			!((code_java_math && code_safe_math)
			   ||(code_safe_math && code_bigint_math)
			   ||(code_java_math && code_bigint_math)
			 ),
			JmlMessages.ARITHMETIC_MODE_CONFLICT
			);
	}
	if(!spec_default)
	{
		check(context,
			!((spec_java_math && spec_safe_math)
			   ||(spec_safe_math && spec_bigint_math)
			   ||(spec_java_math && spec_bigint_math)
			 ),
			JmlMessages.ARITHMETIC_MODE_CONFLICT
			);
	}
	
	CClass prevHost = JmlTypeLoader.getCurrentHostClass();
	try {
	    enterSpecScope(modifiers);

	    // !FIXME! hook to check class-level spec constructs.
	    CClassContextType cctx = delegee.createContext(context);
	    JmlTypeLoader.setCurrentHostClass( (CClass)cctx.findNearestHost() );

	    // !FIXME! Hmm.. maybe be checked in the order they appear
	    // in the source code.
	    for (int i = 0; i < invariants.length; i++) {
		// This try block allows us to display errors from more than 
		// one declaration
		try {
		    invariants[i].typecheck(cctx);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }

	    for (int i = 0; i < constraints.length; i++) {
		// This try block allows us to display errors from more than 
		// one declaration
		try {
		    constraints[i].typecheck(cctx);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }

	    for (int i = 0; i < representsDecls.length; i++) {
		// This try block allows us to display errors from more than 
		// one declaration
		try {
		    representsDecls[i].typecheck(cctx);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }

	    for (int i = 0; i < axioms.length; i++) {
		// This try block allows us to display errors from more than 
		// one declaration
		try {
		    axioms[i].typecheck(cctx);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }

	    for (int i = 0; i < varAssertions.length; i++) {
		// This try block allows us to display errors from more than 
		// one declaration
		try {
		    varAssertions[i].typecheck(cctx);
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }

	    // delegate to the Java typechecker
	    delegee.typecheck( context );
	    
	    // do JML-specific typechecking after delegation

	    combineSpecifications();

	    JFieldDeclarationType[] flds = fields();
	    for (int i = 0; i < flds.length; i++) {
		if (flds[i] instanceof JmlFieldDeclaration) {
		    JmlFieldDeclaration fdecl 
			= (JmlFieldDeclaration) flds[i];
		    if (fdecl.jmlAccess().isStatic()) {
			// static fields were typechecked in a previous 
			// pass before refined fields had been linked 
			// together; so this check is necessary here.
			fdecl.checkRefinementConsistency(context);
		    }
		}
	    }

	    if ( !this.isRefined() ) {
		initializeDataGroupMap();
		String javaFileName = findJavaFileInRefinement();
		if ( javaFileName != null ) {
		    checkMethodsInterface( javaFileName );
		    checkFieldsInterface( javaFileName );
		} else {
		    String thisFileName 
			= this.getTokenReference().file().getName();
		    CTopLevel.getCompiler().reportTrouble(
			new CWarning( getTokenReference(),
				      JmlMessages.CLASS_NOT_DEFINED,
				      this.ident(),
				      thisFileName )
			);
		}
	    }
	}
	finally {
	    JmlTypeLoader.setCurrentHostClass(prevHost);
	    exitSpecScope(modifiers);
	}
    }

    // ---------------------------------------------------------------------
    // CODE GENERATION
    // ---------------------------------------------------------------------

    /**
     * Refactors this to include dispatchers for multimethods and
     * other code necessary for running MultiJava code on a standard
     * JVM.  */
    public void translateMJ( CContextType context )
    {
	delegee.translateMJ( context );
    }

    // -------------------------------------------------------------
    // CompilerPassEnterable
    // -------------------------------------------------------------

    /**
     * Compares this to a given object.
     *
     * <pre><jml>
     * also
     *   requires o instanceof JmlTypeDeclaration;
     *	 ensures (* \result is ordered according to suffix of the source files *);
     * also
     *   requires o != null && !(o instanceof JmlTypeDeclaration);
     *	 signals_only ClassCastException;
     * </jml></pre>
     *
     * @param o an <code>Object</code> value to compare to this
     * @return 0 if this.equals(o)
     * @exception ClassCastException if <code>o</code> is incomparable to this
     */
    public int compareTo(/*@ non_null @*/ Object o) throws ClassCastException {
	JmlTypeDeclaration other = (JmlTypeDeclaration) o;
	CClass clazz = delegee.getCClass();
	int res;
	if ( clazz != null ) {
	    res = clazz.compareTo(other.delegee.getCClass());
	} else {
	    throw new ClassCastException("Cannot compare null reference");
	}
	return res;
    }
    
    //@ protected represents arePassParametersCached <- arePassParametersCached();

    /*@ protected pure model boolean arePassParametersCached() {
      @    return cachedContext == null;
      @ }
      @*/

    /**
     * Caches the arguments for the compiler passes.
     * @see CompilerPassEnterable
     *
     * !FIXME! this spec (or the implementation) is wrong, delegee's
     * state is not changed
     *
     * <pre><jml>
     * also
     *  ensures delegee.arePassParametersCached;
     * </jml></pre> */
    public void cachePassParameters( CContextType context ) {
	cachedContext = context;
    }

    /**
     * Performs preliminary processing on compilation units and types.
     * Processes type imports so external methods' receiver types can
     * be analyzed and supertypes can be resolved.  Groups external
     * methods by name, corresponding to the anchor classes that will
     * eventually be generated.  Mutates the name space management in
     * CTopLevel to record a CGenericFunctionCollection singleton for
     * each anchor class.  */
    public void preprocessDependencies() throws PositionedError {
	preprocessDependencies(cachedContext);
    }

    public void checkInterface() throws PositionedError {
	checkInterface(cachedContext);
    }

    public void checkInitializers() throws PositionedError {
	checkInitializers(cachedContext);
    }

    public void resolveSpecializers() throws PositionedError {
	resolveSpecializers(cachedContext);
    }
        
    public void typecheck() throws PositionedError {
	typecheck(cachedContext);
    }

    public void translateMJ() {
	translateMJ(cachedContext);
    }

    //---------------------------------------------------------------------
    // REFINEMENT
    //---------------------------------------------------------------------

    /**
     * Registers that the given type declaration, <code>refinedType</code>,
     * is refined by this type declaration.
     */
    public void setRefinedType( JmlBinaryType refinedType )
    {
	this.setRefinedMember(refinedType);
	refinedType.setRefiningMember(this);
	JmlSourceClass selfSrc = (JmlSourceClass) this.getCClass();
	JmlSourceClass refinedSrc = (JmlSourceClass) refinedDecl.getCClass();
	selfSrc.setRefinedType(refinedSrc);
    }

    /**
     * Registers that the given type declaration, <code>refinedType</code>,
     * is refined by this type declaration.
     */
    public void setRefinedType( JmlTypeDeclaration refinedType )
	throws PositionedError 
    {
	checkForCycles(refinedType);
	// not set if there is a cycle (throws an exception)
	this.setRefinedMember(refinedType);
	refinedType.setRefiningType(this);
	JmlSourceClass selfSrc = (JmlSourceClass) this.getCClass();
	JmlSourceClass refinedSrc = (JmlSourceClass) refinedDecl.getCClass();
	selfSrc.setRefinedType(refinedSrc);
    }

    /**
     * Sets the <code>refinedType</code> field of this 
     * <code>JmlTypeDeclaration</code> object.
     * Throws an exception if setting this field would have created 
     * a cycle in the refinement sequence.  
     */
    private void checkForCycles(JmlTypeDeclaration refinedType)
	throws PositionedError 
    {
	// Check for cycles in the refinement hierarchy before setting this
	// field.
	JmlMemberDeclaration nextType = this;
	while (nextType != null) {
	    if ( nextType == refinedType ) {
		String thisFileName = getTokenReference().file().getName();
		throw new PositionedError( getTokenReference(),
					   JmlMessages.REFINE_FILE_CYCLE, 
					   thisFileName, 
					   nextType.getCClass()
					       .sourceFile().getName()
					   );
	    }
	    nextType = nextType.getRefinedMember();
	}

	nextType = this.getRefiningMember();
	while (nextType != null) {
	    if ( nextType == refinedType ) {
		String thisFileName = getTokenReference().file().getName();
		throw new PositionedError( getTokenReference(),
					   JmlMessages.REFINE_FILE_CYCLE, 
					   thisFileName, 
					   nextType.getCClass()
					       .sourceFile().getName()
					   );
	    }
	    nextType = nextType.getRefiningMember();
	}
    }

    private void setRefiningType(JmlTypeDeclaration refiningDecl) {
	this.refiningDecl = refiningDecl;
    }

    private void checkFieldsInterface( String javaFileName ) 
    {
	for (int i=0; i<combinedFields.length; i++) {
	    JmlFieldDeclaration nextField 
		= (JmlFieldDeclaration) combinedFields[i];

	    JmlMemberDeclaration nextMemb = nextField;
	    boolean isDeclaredInNonJavaFile = false;
	    boolean isDeclaredInJavaFile = false;
	    while (nextMemb != null) {
		boolean inJava = nextMemb.inJavaFile();
		isDeclaredInNonJavaFile = isDeclaredInNonJavaFile || !inJava;
		isDeclaredInJavaFile = isDeclaredInJavaFile || inJava;

		nextMemb = nextMemb.getRefinedMember();
	    }

	    if ( isDeclaredInNonJavaFile && !isDeclaredInJavaFile ) {
		// This field is declared in a non-java file
		// of the refinement chain but not in a java file.
		// Only model and ghost fields can be declared this way. 
		if (! (nextField.jmlAccess().isModel() 
		       || nextField.jmlAccess().isGhost()) ) {
		    CTopLevel.getCompiler().reportTrouble(
				new PositionedError( 
				     nextField.getTokenReference(),
				     JmlMessages.NON_MODEL_FIELD_NOT_DEFINED,
				     nextField.ident(),
				     javaFileName )
				);
		}
	    }

	}
	if ( ! jmlAccess().isAbstract() && ! jmlAccess().isModel() 
	     && ! this.isInterface() ) {
	    checkModelFields( getModelFields() );
	    checkModelFields( getAllInterfaceModelFields() );
	    if (this instanceof JmlClassDeclaration) {
		checkModelFields( getAllSuperClassModelFields() );
	    }
	}
    }

    private void checkModelFields( JFieldDeclarationType[] modelFields ) 
    {
    	for (int i=0; i<modelFields.length; i++) {
    		CType typ = modelFields[i].getType();
    		if (! typ.toString()
    				.equals("org.jmlspecs.lang.JMLDataGroup") ) {
    			JmlTypeDeclaration repType 
    			= findTypeWithRepresentsFor(modelFields[i].getField());
    			if (repType == null) {
    				if(Main.jmlOptions.noRepresentsAsError()){
    					CTopLevel.getCompiler().reportTrouble(
    							new PositionedError( 
    									getTokenReference(),
    									JmlMessages.MISSING_REPRESENTS_ERROR,
    									modelFields[i].ident(),
    									modelFields[i].getTokenReference() )
    							);
    				}
    				else{
    					CTopLevel.getCompiler().reportTrouble(
    							new CWarning( 
    									getTokenReference(),
    									JmlMessages.MISSING_REPRESENTS,
    									modelFields[i].ident(),
    									modelFields[i].getTokenReference() )
    							);
    				}
    			}
    		}
    	}
    }

    private void typecheckSuperTypes() {
	JmlSourceClass self = (JmlSourceClass) this.getCClass();
	CClass superClass = self.getSuperClass();
	if (superClass instanceof JmlSourceClass) {
	    JmlTypeLoader.getJmlSingleton()
		.activateTypeCheck(superClass.qualifiedName());
	}
	CClassType[] interfaces = self.getInterfaces();
	for (int i = 0; i < interfaces.length; i++) {
	    CClass nextInterface = interfaces[i].getCClass();
	    if (nextInterface instanceof JmlSourceClass) {
		JmlTypeLoader.getJmlSingleton()
		    .activateTypeCheck(nextInterface.qualifiedName());
	    }
	}
    }

    private void checkMethodsInterface( String javaFileName ) 
    {
	JmlMemberDeclaration nextMemb;
	JmlMethodDeclaration meth;
	for (int i=0; i<combinedMethods.length; i++) {
	    nextMemb = combinedMethods[i];
	    if ( nextMemb.inBinaryClassFile() ) {
		// This means this method is only declared in a 
		// '.class' file so skip the rest of the checking, 
		// but give a warning message if appropriate.

		if ( !nextMemb.ident().equals(JAV_STATIC_INIT)
		     && !nextMemb.jmlAccess().isPrivate() ) {

		    String fileName 
			= nextMemb.getTokenReference().file().getName();
		    CTopLevel.getCompiler().reportTrouble(
			new CWarning( getTokenReference(),
				      JmlMessages.METHOD_NOT_DEFINED,
				      nextMemb.stringRepresentation(),
				      fileName )
			);
		}

	    } else {
		meth = (JmlMethodDeclaration) nextMemb;

		JmlMethodDeclaration declWithBody = meth.findDeclWithBody();

		CMethodSet overriddenMethodSet = meth.overriddenMethods();
		boolean overrides = (overriddenMethodSet != null
				     && !overriddenMethodSet.isEmpty());

		if (!overrides) {

		    boolean isDeclaredInJavaFile = false;
		    boolean isDeclaredInNonJavaFile = false;
		    while (nextMemb != null) {
			boolean inJava = nextMemb.inJavaFile();
			isDeclaredInNonJavaFile 
			    = isDeclaredInNonJavaFile || !inJava;
			isDeclaredInJavaFile 
			    = isDeclaredInJavaFile || inJava;

			nextMemb = nextMemb.getRefinedMember();
		    }

		    if ( isDeclaredInNonJavaFile && !isDeclaredInJavaFile ) {
			// This method is declared in a non-java file
			// of the refinement chain but not in a java file.
			// Only model method specifications can be declared 
			// without being part of a type's interface.
			if (! meth.jmlAccess().isModel() ) {
			    CTopLevel.getCompiler().reportTrouble(
				new PositionedError( 
				     meth.getTokenReference(),
				     JmlMessages.NON_MODEL_METHOD_NOT_DEFINED,
				     meth.stringRepresentation(),
				     javaFileName )
				);
			}
		    }
		}
	    }
	}
    }

    public void checkAssignableClauses()
    		throws PositionedError {
    	// To check the assignable clauses, the super class and 
    	// implemented interfaces have to be type checked first.

    	// System.out.println("checking assignable clauses for type: "+this.ident());
    	typecheckSuperTypes();

    	JmlMethodDeclaration meth;
    	if(combinedMethods != null)
    	for (int i=0; i<combinedMethods.length; i++) {
    		if (! combinedMethods[i].inBinaryClassFile()) {
    			meth = (JmlMethodDeclaration) combinedMethods[i];
    			meth.checkAssignableFields( dataGroupMap );
    		}
    	}

    	JmlTypeDeclaration innerType;
    	if(combinedInners != null)
    	for (int i=0; i<combinedInners.length; i++) {
    		if (! combinedInners[i].inBinaryClassFile()) {
    			innerType = (JmlTypeDeclaration) combinedInners[i];
    			innerType.checkAssignableClauses();
    		}
    	}	
    }

    //---------------------------------------------------------------------
    // COMBINE SPECIFICATIONS
    //---------------------------------------------------------------------

    public /*@ pure @*/ JFieldDeclarationType[] getCombinedFields()
    {
	return combinedFields;
    }

    public /*@ pure @*/ JmlMemberDeclaration[] getCombinedMethods()
    {
	return combinedMethods;
    }

    public /*@ pure @*/ JmlMemberDeclaration[] getCombinedInners()
    {
	return combinedInners;
    }

    public void setMembersToCombinedMembers() {
	combineSpecifications();
	combineFieldModifiersAndSetInitializer();
	combineMethodModifiersAndSetBody();
	combineFieldAndMethodModifiersOfNestedTypes();

	// set fields, methods, and inner classes to the combined members
	setFieldsOnly(combinedFields);
	setMethods(methodList);
	setInners(innerList);

	invariants = combinedInvariants;
	constraints = combinedConstraints;
	representsDecls = combinedRepresentsDecls;
	axioms = combinedAxioms;
	varAssertions = combinedVarAssertions;
    }
    
    private void combineFieldModifiersAndSetInitializer() {
	JmlMemberDeclaration currField;

	for (int i=0; i<combinedFields.length; i++) {
	    JmlFieldDeclaration fdecl
		= (JmlFieldDeclaration) combinedFields[i];
	    long modifiers = fdecl.modifiers();

	    currField = fdecl.getRefinedMember();

	    // combine modifiers 
	    while (currField != null) {
		modifiers |= currField.modifiers();
		currField = currField.getRefinedMember();
	    }

	    // Search the refinement hierarchy for the field initializer
	    // Set the field initializer of the most refined decl
	    if (! fdecl.hasInitializer()) {
		JmlFieldDeclaration declWithInit 
		    = fdecl.findDeclWithInitializer();
		if (declWithInit != null) {
		    fdecl.setInitializer(declWithInit.getInitializer());
		}
	    }

	    fdecl.setModifiers(modifiers);
	    fdecl.setSpecstoCombinedSpecs();
	}
    }

    private void combineMethodModifiersAndSetBody() 
    {
	JmlMemberDeclaration refMeth;

	methodList.clear();

	for (int i=0; i<combinedMethods.length; i++) {
	    JmlMemberDeclaration memb = combinedMethods[i];

	    if ( !memb.inBinaryClassFile() ) {
		// remove the JmlBinaryMethod members that come 
		// from .class files (since other tools can't handle 
		// them)
		methodList.add(memb);
		JmlMethodDeclaration meth = (JmlMethodDeclaration) memb;
		// System.out.println("meth:" + meth.ident());

		// Search the refinement hierarchy for the method body
		// Set the body of the most refined decl
		if (! meth.hasBody()) {
		    JmlMethodDeclaration declWithBody = meth.findDeclWithBody();
		    if (declWithBody != null) {
			meth.setBody(declWithBody.body());
		    }
		}
		combineParameterModifiers( meth );
		meth.setSpecstoCombinedSpecs();
	    }
	}
	if (methodList.size() != combinedMethods.length) {
	    combinedMethods = new JmlMemberDeclaration[methodList.size()];
	    methodList.toArray(combinedMethods);
	}
	
    }

    private void combineParameterModifiers( JmlMethodDeclaration meth ) 
    {
	JFormalParameter[] parms = meth.parameters();

	JmlMemberDeclaration refMeth = meth.getRefinedMember();
	while (refMeth != null) {
	    // combine modifiers (e.g., non_null) for return and 
	    // argument types.
	    meth.setModifiers(meth.modifiers() | refMeth.modifiers());

	    if (! refMeth.inBinaryClassFile()) {
		// not a binary method declaration (not in a .class file)
		JFormalParameter[] parmsFrom 
		    = ((JmlMethodDeclaration)refMeth).parameters();
		for (int i = 0; i < parms.length; i++ ) {
		    if (parms[i] instanceof JmlFormalParameter) {
			// we have to check the type of parms[i] 
			// because when an inner class is non-static 
			// 'this' is passed to constructors and 
			// its type is JFormalParameter (we just skip 
			// this case since it can never be non_null).
			JmlFormalParameter pt 
			    = (JmlFormalParameter) parms[i];
			JmlFormalParameter pf 
			    = (JmlFormalParameter) parmsFrom[i];
			// Chalin - FIXME - this seems useless since
			// we require that parameters of refined methods match
			// exactly w.r.t. nullity.  For now I will simply double check.
			// was: pt.setNonNull(pt.isNonNull() | pf.isNonNull());
	    		if (pt.isDeclaredNonNull() != pf.isDeclaredNonNull())
			    throw new IllegalStateException("meth = "
							    + meth.stringRepresentation()
							    + "; refining meth = "
							    + meth.getRefinedMember()
							    .stringRepresentation());
		    }
		}
	    }
	    refMeth = refMeth.getRefinedMember();
	}
    }

    private void combineFieldAndMethodModifiersOfNestedTypes()
    {
	JmlTypeDeclaration innerType;
	for (int i=0; i<combinedInners.length; i++) {
	    if (! combinedInners[i].inBinaryClassFile()) {
		innerType = (JmlTypeDeclaration) combinedInners[i];
		innerType.setMembersToCombinedMembers();
	    }
	}
    }

    public void combineSpecifications() 
    {
	if (hasBeenCombinedWithRefinedDecl) {
	    return;
	}

	if (refinedDecl != null) {
	    this.getRefinedMember().combineSpecifications();
	}

	// Combine methods, constructors, and their specifications

	combineMethodSpecs();
	includeAllMethods();

	// Combine all of the field definitions.

	combineFieldSpecs();
	includeAllFields();

	// Combine inners

	combineNestedClassSpecs();
	includeAllNestedClasses();

	// Combine all of the class specifications
	// invariants, constraints, representsDecls, axioms,
	// and varAssertions

	combineClassSpecs();

	hasBeenCombinedWithRefinedDecl = true;
    }
    
    /**
     * Links the fields in a refinement chain of this 
     * <code>JmlTypeDeclaration</code> object.
     */
    private void linkFieldRefinements() 
    {
	JFieldDeclarationType[] flds = fields();
	for (int i = 0; i < flds.length; i++) {
	    if (flds[i] instanceof JmlFieldDeclaration) {
		JmlFieldDeclaration fdecl = (JmlFieldDeclaration) flds[i];
		fdecl.setRefinementLinks();
	    }
	}
    }
    /**
     * Links the methods in a refinement chain of this 
     * <code>JmlTypeDeclaration</code> object.
     */
    private void linkMethodRefinements() 
    {
	JmlMethodDeclaration mdecl
	    = (JmlMethodDeclaration) getDefaultConstructor();
	if (mdecl != null) {
	    mdecl.setRefinementLinks();
	}
	ArrayList methods = methods();
	Iterator iter = methods.iterator();
	while (iter.hasNext()) {
	    mdecl = (JmlMethodDeclaration) iter.next();
	    mdecl.setRefinementLinks();
	}
    }
    /**
     * Links the inner types of a refinement chain of this 
     * <code>JmlTypeDeclaration</code> object.
     */
    private void linkInnerTypeRefinements()
	throws PositionedError
    {
	// set the link between the inner type declarations
	JmlSourceClass selfSrc = (JmlSourceClass) delegee.getCClass();
	ArrayList inners = new ArrayList(inners());
	Iterator iter = inners.iterator();
	while (iter.hasNext()) {
	    JmlTypeDeclaration innerDecl = (JmlTypeDeclaration) iter.next();
	    JmlSourceClass innerSrc = (JmlSourceClass) innerDecl.getCClass();
	    JmlSourceClass refinedSrc 
		    = selfSrc.lookupRefinedInnerType(innerSrc);

	    if (refinedSrc != null) {
		JmlMemberDeclaration refinedDecl = refinedSrc.getAST();
		if (refinedDecl.inBinaryClassFile()) {
		    innerDecl.setRefinedType((JmlBinaryType)refinedDecl);
		} else {
		    innerDecl.setRefinedType((JmlTypeDeclaration)refinedDecl);
		}
	    }
	}
	
    }
    private void combineMethodSpecs() 
    {
	ArrayList methods = methods();
	Iterator iter = methods.iterator();
	while (iter.hasNext()) {
	    JmlMethodDeclaration mdecl = (JmlMethodDeclaration) iter.next();
	    mdecl.combineSpecifications();
	}
    }
    
    private void includeAllMethods() 
    {
	if (combinedMethods != null) {
	    // have already been combined
	    return;
	}
        
        methodList = methods();

        // take into account of the default constructor if this is
        // declared in a Java file (i.e., .java file).
        if (inJavaFile()) {
            JConstructorDeclarationType dc = delegee.getDefaultConstructor();
            if (dc != null) {
                methodList.add(dc);
            }
        }

	if ( this.isRefiningMember()) {
	    JmlMemberDeclaration refinedType = getRefinedMember();
	    refinedType.combineSpecifications();
	    JmlMemberDeclaration[] refMethods;
	    if ( refinedType.inBinaryClassFile() ) {
		// refinedType instanceof JmlBinaryType
		refMethods 
		    = ((JmlBinaryType)refinedType).getCombinedMethods();
	    } else {
		refMethods 
		    = ((JmlTypeDeclaration)refinedType).getCombinedMethods();
	    }
	    for (int i=0; i<refMethods.length; i++) {
		JmlMemberDeclaration refMeth = refMethods[i];
		if (! refMeth.isRefined() ) {
		    // This means that this method was declared in a 
		    // previous declaration of the refinement chain 
		    // and therefore must be added.
		    methodList.add(refMeth);
		}
	    }
	}
	combinedMethods = new JmlMemberDeclaration[methodList.size()];
	methodList.toArray(combinedMethods);
    }

    private void combineFieldSpecs() 
    {
	JFieldDeclarationType[] fs = fields();
	for (int i=0; i<fs.length; i++) {
	    JmlFieldDeclaration fdecl = (JmlFieldDeclaration) fs[i];
	    fdecl.combineSpecifications();
	}
    }
    
    private void includeAllFields() 
    {
	if (combinedFields != null) {
	    // have already been combined
	    return;
	}
	combinedFields = fields();
	if (! this.isRefiningMember()) {
	    return;
	}

	JmlMemberDeclaration refinedMem = getRefinedMember();
	if (! refinedMem.inBinaryClassFile()) {
	    JmlTypeDeclaration refinedType = (JmlTypeDeclaration) refinedMem;
	    refinedType.combineSpecifications();
	    JFieldDeclarationType[] refFields = refinedType.getCombinedFields();
	    ArrayList allFields 
		= new ArrayList(combinedFields.length
					 + refFields.length);
	    for (int i=0; i<combinedFields.length; i++) {
		allFields.add(combinedFields[i]);
	    }
	    for (int i=0; i<refFields.length; i++) {
		JmlFieldDeclaration currField 
		    = (JmlFieldDeclaration) refFields[i];
		if (! currField.isRefined()) {
		    // This means this field is not declared here
		    // and therefore must be added
		    allFields.add(refFields[i]);
		}
	    }
	    combinedFields = new JFieldDeclarationType[allFields.size()];
	    allFields.toArray(combinedFields);
	    
	}
    }

    private void combineNestedClassSpecs() 
    {
	ArrayList inners = inners();
	Iterator iter = inners.iterator();
	while (iter.hasNext()) {
	    JmlTypeDeclaration tdecl = (JmlTypeDeclaration) iter.next();
	    tdecl.combineSpecifications();
	}
    }

    private void includeAllNestedClasses() {
	if (combinedInners != null) {
	    // have already been combined
	    return;
	}
	innerList = inners();
	if ( this.isRefiningMember()) {
	    JmlMemberDeclaration refinedMem = getRefinedMember();
	    refinedMem.combineSpecifications();
	    if (! refinedMem.inBinaryClassFile()) {
		JmlTypeDeclaration refinedType 
		    = (JmlTypeDeclaration) refinedMem;
		JmlMemberDeclaration[] refInners 
		    = refinedType.getCombinedInners();
		for (int i=0; i<refInners.length; i++) {
		    if (! refInners[i].isRefined()) {
			// This means this inner type is not declared here
			// and therefore must be added
			innerList.add(refInners[i]);
		    }
		}
	    }
	}
	combinedInners = new JmlMemberDeclaration[innerList.size()];
	innerList.toArray(combinedInners);
    }

    private void combineClassSpecs() {
	JmlMemberDeclaration refinedMem = getRefinedMember();
	if (refinedMem == null || refinedMem.inBinaryClassFile()) {
	    combinedInvariants = invariants;
	    combinedConstraints = constraints;
	    combinedRepresentsDecls = representsDecls;
	    combinedAxioms = axioms;
	    combinedVarAssertions = varAssertions;
	    return;
	} else {
	    JmlTypeDeclaration refinedType = (JmlTypeDeclaration) refinedMem;
	    combinedInvariants = (JmlInvariant[]) Utils
		.combineArrays(invariants, 
			       refinedType.combinedInvariants());
	    combinedConstraints = (JmlConstraint[]) Utils
		.combineArrays(constraints, 
			       refinedType.combinedConstraints());
	    combinedRepresentsDecls = (JmlRepresentsDecl[]) Utils
		.combineArrays(representsDecls, 
			       refinedType.combinedRepresentsDecls());
	    combinedAxioms = (JmlAxiom[]) Utils
		.combineArrays(axioms, 
			       refinedType.combinedAxioms());
	    combinedVarAssertions = (JmlVarAssertion[]) Utils
		.combineArrays(varAssertions, 
			       refinedType.combinedVarAssertions());
	}
    }

    /** Checks if every method is rac-compilable. That is, checks that
     * all concrete methods have body. */
    public boolean checkRacability(
        org.multijava.util.compiler.Compiler compiler) {
        boolean ok = true;
        for (Iterator i = methods().iterator(); i.hasNext(); ) {
	    JmlMethodDeclaration m = (JmlMethodDeclaration)(i.next());
            if (!(m.isAbstract() || m.hasBody() || m.isModel()
                  || m.isNative())) {
                compiler.reportTrouble(new PositionedError(
                    m.getTokenReference(),
                    MjcMessages.METHOD_NOBODY_NOABSTRACT));
                ok = false;
            }
        }
        return ok;
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private CContextType cachedContext;

    /*@ spec_public @*/ private JTypeDeclaration delegee;
    private /*@ non_null */ JmlMemberAccess jmlAccess = null;
    

    protected /*@ non_null */ boolean[] interfaceWeaklyFlags;
    protected /*@ non_null */ JmlInvariant[] invariants;
    protected /*@ non_null */ JmlConstraint[] constraints;
    protected /*@ non_null */ JmlRepresentsDecl[] representsDecls;
    protected /*@ non_null */ JmlAxiom[] axioms;
    protected /*@ non_null */ JmlVarAssertion[] varAssertions;

    //---------------------------------------------------------------------
    // COMBINED REFINEMENT DATA
    //---------------------------------------------------------------------

    protected /*@ non_null */ JmlInvariant[] combinedInvariants;
    protected /*@ non_null */ JmlConstraint[] combinedConstraints;
    protected /*@ non_null */ JmlRepresentsDecl[] combinedRepresentsDecls;
    protected /*@ non_null */ JmlAxiom[] combinedAxioms;
    protected /*@ nullable */ JmlVarAssertion[] combinedVarAssertions = null;

    /**
     * The fields declared within the type represented by this,
     * extracted from fieldsAndInits at initialization time 
     * and combined with any declarations refined by this type. 
     */
    private	/*@ nullable */ JFieldDeclarationType[]	combinedFields = null;

    protected	/*@ nullable */ ArrayList methodList = null;
    protected	/*@ nullable */ JmlMemberDeclaration[] combinedMethods = null;

    protected	/*@ nullable */ ArrayList innerList = null;
    protected	/*@ nullable */ JmlMemberDeclaration[] combinedInners = null;

    protected	/*@ nullable */ JFieldDeclarationType[] modelFields = null;
    protected	/*@ nullable */ JFieldDeclarationType[] superClassModelFields = null;
    protected	/*@ nullable */ JFieldDeclarationType[] interfaceModelFields = null;

    protected	/*@ nullable */ JmlDataGroupMemberMap dataGroupMap = null;

    /** Indicates whether this type declaration has a source file in
     * the refinement chain. This field is used by jmlrac. */
    private boolean hasSourceInRefinement;

    protected boolean hasBeenCombinedWithRefinedDecl = false;
}

