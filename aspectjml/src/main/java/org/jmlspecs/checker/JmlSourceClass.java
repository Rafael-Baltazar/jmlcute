/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
 * *
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
 * $Id: JmlSourceClass.java,v 1.52 2007/02/08 14:05:49 leavens Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;

import org.jmlspecs.util.classfile.JmlClassInfo;
import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CAbstractMethodSet;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CField;
import org.multijava.mjc.CFieldTable;
import org.multijava.mjc.CMember;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.util.Utils;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.FieldInfo;
import org.multijava.util.classfile.MethodInfo;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * A class for representing JML classes read from *.java files.  It is
 * primarily just a data structure, apart from methods for generating
 * the qualified name and for determining whether the member is
 * accessible from some class.
 *
 * @see	CMember
 */
public class JmlSourceClass extends CSourceClass 
    implements JmlModifiable, Constants
{
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a class export from source
     */
    public JmlSourceClass(org.multijava.mjc.Main compiler, 
			  CClass owner, CMemberHost host,
			  TokenReference where, long modifiers, String ident,
			  String qualifiedName, CTypeVariable[] typevariables,
              boolean isAnonymous, boolean isMember, boolean deprecated )
    {
	super(compiler, new JmlMemberAccess( owner, host, modifiers ),
	      where, ident, qualifiedName, typevariables, 
	      isAnonymous, isMember, deprecated);
	if ( where != null ) {
	    levelNumber = computeSuffixNumber(where.name());
	}
    }

    // ----------------------------------------------------------------------
    // TYPE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Returns the super class of this class
     */
    public /*@ pure @*/ CClass getSuperClass() {
	CClass superClass = super.getSuperClass();
	if (superClass instanceof JmlSourceClass) {
	    superClass = ((JmlSourceClass)superClass).getMostRefined();
	}
	return superClass;
    }

    /**
     *  This method ensures that a file at a lower level only refines 
     *  a file at the same or higher level; but this check is only done 
     *  on the most refined definition of a class. 
     *  Also, the most refined definition of a class must be declared 
     *  in a file with the same name as the class so it will be found by 
     *  the type checker when that class is loaded.  
     *  The level number is based on the suffix of the source file, see 
     *  method <code>computeSuffixNumber</code>.  
     */
    public void checkFileNameAndSuffix(JmlSourceClass refinedType) 
	throws UnpositionedError 
    {
	if ( ! this.isRefined() && this.isRefiningType() ) {
	    
	    // this is the most refined declaration of this type

	    // make sure the file name matches the type name
	    String thisFileName = this.sourceFile().getName();
	    int pos = thisFileName.lastIndexOf('.');
	    String filePrefix = thisFileName.substring(0, pos);
	    if (!this.ident().equals(filePrefix)) {
		throw new UnpositionedError(
				 JmlMessages.CLASS_NAME_REFINING_FILENAME, 
				 this.ident(), 
				 thisFileName
				 );
	    }

	    // make sure the suffix is the most active in the chain
	    JmlSourceClass nextClass = getRefinedType();
	    while (nextClass != null) {
		if ( this.levelNumber > nextClass.getLevelNumber() ) {
		     throw new UnpositionedError(
				 JmlMessages.INVALID_REFINE_FILE_SUFFIX, 
				 thisFileName, 
				 nextClass.sourceFile().getName()
				 );
		}
		nextClass = nextClass.getRefinedType();
	    }
	}
    }

    /**
     * Returns the refined 'JmlSourceClass' for this class
     */
    public JmlSourceClass getRefinedType() {
	return this.refinedSourceClass;
    }

    /**
     * Returns the refining 'JmlSourceClass' for this class
     */
    public JmlSourceClass getRefiningType() {
	return this.refiningSourceClass;
    }

    /** Returns true if the calling object is more refined (perhaps
	in more than one step) than the argument;  Returns false
	if they are the same object or the calling argument is
	less refined or they are not part of the same refinement
	seqeuence.
    */
    public boolean isMoreRefinedThan(JmlSourceClass j) {
	JmlSourceClass t = getRefinedType();
	while (t != null && t != j) t = t.getRefinedType();
	return t == j;
    }
    /**
     * Sets the <code>refinedType</code> field of this 
     * <code>JmlSourceClass</code> object.
     * Throws an exception if setting this field would have created 
     * a cycle in the refinement sequence.  
     */
    public void setRefinedType(JmlSourceClass refinedType)
    {
	this.refinedSourceClass = refinedType;
	refinedType.refiningSourceClass = this;
    }

    public boolean isRefiningType() {
	return refinedSourceClass != null;
    }

    public boolean isRefined() {
	return refiningSourceClass != null;
    }

    public /*@ pure @*/ JmlSourceClass getMostRefined() {
	if (refiningSourceClass == null) {
	    return this;
	} else {
	    return refiningSourceClass.getMostRefined();
	}
    }

    public int classesRefined() {
	if (refinedSourceClass == null) {
	    return 0;
	} else {
	    return refinedSourceClass.classesRefined() + 1;
	}
    }

    /**
     * Sets the AST for this method.
     */
    public void setAST(JmlMemberDeclaration typeAST) 
    {
	this.typeAST = typeAST;
    }

    /**
     * Returns the AST for this method.
     */
    public JmlMemberDeclaration getAST() {
	return typeAST;
    }


    /**
     * Compares this to a given object.
     *
     * <pre><jml>
     * also
     *   requires (o instanceof JmlSourceClass) &&
     *     qualifiedName().equals(((JmlSourceClass)o).qualifiedName());
     *	 ensures (* \result is ordered according to suffix of the source files *);
     *  also
     *   requires o != null && !(o instanceof JmlSourceClass);
     *   signals_only ClassCastException;
     * </jml></pre>
     *
     * @param o an <code>Object</code> value to compare to this
     * @return 0 if this.equals(o)
     * @exception ClassCastException if <code>o</code> is incomparable to this
     */
    public /*@ pure @*/ int compareTo(/*@ non_null @*/ Object o)
            throws ClassCastException {
	JmlSourceClass other = (JmlSourceClass) o;
	if ( this.qualifiedName().equals(other.qualifiedName()) ) {
	    // they have the same fully qualified name
	    return this.compareLevelsTo( other );
	}
	int res = super.compareTo(o);
	return res;
    }

    protected /*@ pure @*/ int compareLevelsTo( JmlSourceClass other ) {
	if ( this.levelNumber == other.levelNumber ) {
	    if (this.refines(other)) {
		return -1;
	    } else {
		return 1;
	    }
	} else {
	    return this.levelNumber - other.getLevelNumber();
	}
    }

    public /*@ pure @*/ int getLevelNumber( ) {
	return levelNumber;
    }

    /**
     * Indicates whether this host is a subclass of the given class,
     * where "subclass" is the reflexive, transitive closure of the
     * extends relation.
     *
     * @param	maybeSuper	the potential superclass
     */
    public boolean descendsFrom( CClass maybeSuper ) {

	finishSymbolTable();
	if( super.descendsFrom(maybeSuper) ) {
	    return true;
	} else if( maybeSuper instanceof JmlSourceClass ) {
	    // this is necessary to handle refinement
	    // i.e., when this refines maybeSuper.
	    JmlSourceClass maybeRefined = (JmlSourceClass) maybeSuper;
	    return this.refines(maybeRefined);
	} else {
	    return false;
	}
    }

    // This method is required to handle the inheritance involved 
    // in refinement. 
    protected /*@ pure @*/ boolean refines( Object maybeRefined ) {
	if (maybeRefined == this) {
	    return true;
	} else if (refinedSourceClass == null) {
	    // no more refined types
	    return false;
	} else if (refinedSourceClass.refines(maybeRefined)) {
	    return true;
	} else {
	    CClassType[] interfaces = getInterfaces();
	    if (interfaces != null) {
		for (int i = 0; i < interfaces.length; i++) {
		    CClass currType = interfaces[i].getCClass();
		    if (currType instanceof JmlSourceClass) {
			if (((JmlSourceClass) currType).refines(maybeRefined)) {
			    return true;
			}
		    }
		}
	    }

	    return false;
	}
    }

    /**
     * Searches a field in current class and parent hierarchy as needed
     * @param name the simple name of the field
     * @param context the context in which the reference appears, used 
     *		      for accessibility checks	
     * @exception UnpositionedError this error will be positioned soon
     */
    protected CField lookupFieldHelper(String name,
				       CExpressionContextType context) 
	throws UnpositionedError 
    {
	CField field = null;
	try {
	    stackLevel++;
	    finishSymbolTable();
	    field = super.lookupFieldHelper(name, context);

	    // model fields are not visible from non-spec part (Java code)
	    if ( (field instanceof JmlModifiable) &&
		 ((JmlModifiable)field).isEffectivelyModel() &&
		 !JmlContext.inSpecScope()) {

		modelField = field;
		field = lookupSuperField(name, context);
	    }
	}
	finally {
	    stackLevel--;
	    // Counting the stack frames was easier than 
	    // converting from a recursive algorithm (in MJC) 
	    // to an iterative algorithm (needed so we know when 
	    // the lookup is finished).
	    if (stackLevel == 0) {
		// the lookup is finished
		if ( modelField != null && field == null ) {
		    // found an effectively model field but no concrete field
                    //@ assert !JmlContext.inSpecScope();
                    // !FIXME! this really should be an error, not a warning!
                    CField mf = modelField;
                    modelField = null;  // set up modelField for next call
		    throw new
                        UnpositionedError((((JmlModifiable)mf).isModel()
                                           ? JmlMessages.MODEL_FIELD_ACCESS
                                           : JmlMessages.GHOST_FIELD_ACCESS),
                                          name, 
                                          mf.host());
		}
		modelField = null;
	    }
	}
	return field;
    }

    /**
     * Returns the signature of the field with the given name declared
     * in this class, or null if this class does not declare a field
     * with the given name. 
     * 
     * If not found in this class object, continue looking in any 
     * refined JmlSourceClass objects.
     */
    protected /*@ pure @*/ CField getDeclaredField( String ident) {
	CField field = super.getDeclaredField(ident);
	if( field == null ) {
	    if ( refinedSourceClass != null ) {
		field = refinedSourceClass.getDeclaredField(ident);
	    }
	}
	return field;
    }

    /**
     * Returns true iff a field with same name is already defined in a 
     * superclass or an implemented interface.
     *
     * @param	ident		the name of the field
     */
    protected boolean isFieldRedefined( String ident, 
					CExpressionContextType dummyContext ) 
	throws UnpositionedError 
    {
	boolean result = false;

	    try {
		JmlContext.enterSpecScope();
		result = super.isFieldRedefined( ident, dummyContext );
	    }
	    finally {
		JmlContext.exitSpecScope();
	    }

	return result;
    }

    /**
     * Indicates whether this is accessible from the given host.
     *
     * @param	from	the host that wants access
     * @return	true iff the given host is allowed access to this host's 
     *		members
     */
    public /*@ pure @*/ boolean isAccessibleFrom( CMemberHost from ) {
	boolean result = super.isAccessibleFrom(from);
	if (result && isEffectivelyModel()) {
	    result = JmlContext.inSpecScope();
        }
	return result;
    }

    /** 
     * Indicates whether the declaration of this member is local to
     * the given host.  It adds another case to the two cases handled 
     * by the super class CMember: 
     * (See method isLocalTo in {@link CMember} for an explanation of 
     * those two cases).  The additional case involves refinement and 
     * is necessary for private fields, methods, and classes 
     * declared inside a class declaration refined by the host of 
     * this member.  
     * 
     *<OL>
     *
     * <LI>If the given host is a class, then this member 
     * is local to the given host if the given host class refines the 
     * declaration where this member appears.</LI>
     *
     * </OL>
     *
     * @param	from		the given host
     *
     */
    public boolean isLocalTo( CMemberHost from ) {
	if ( super.isLocalTo( from ) ) {
	    return true;
	} else if (from instanceof JmlSourceClass) {
	    CMemberHost myHost = access().host();
	    JmlSourceClass fromClass = (JmlSourceClass) from;
	    return fromClass.refines(myHost);
	}
	return false;
    }

    /**
     * Returns true iff this class should be treated as a model class;
     * the class itself is defined as model or it is defined in a 
     * model class or interface.
     */
    public /*@ pure @*/ boolean isEffectivelyModel() {
	return isModel() ||
	    (owner() != null && ((JmlModifiable)owner()).isEffectivelyModel());
    }

    /**
     * returns true iff this class is explicitly annotated with the model
     * modifier.
     */
    public /*@ pure @*/ boolean isModel() {
        return jmlAccess().isModel();
    }

    /**
     * returns true iff this class is explicitly annotated with the ghost
     * modifier.
     */
    public /*@ pure @*/ boolean isGhost() {
        return jmlAccess().isGhost();
    }

    /**
     * Returns a list of abstract methods. This method is called to check
     * whether all abstract methods are implemented by the concrete class
     * being type-checked. Thus, it is refined here to return only non-model
     * methods.
     */
    public CMethodSet.MethodArgsPair[] getAbstractMethods() {

	CMethodSet.MethodArgsPair[] methods = filterModelMethods(super.getAbstractMethods());
	if( refinedSourceClass != null ) {
	    CMethodSet.MethodArgsPair[] refinedMethods
		= refinedSourceClass.getAbstractMethods();
	    // no need to filter since done in the above call
	    if ( refinedMethods.length == 0 ) {
		return methods;
	    } else if ( methods.length == 0 ) {
		return refinedMethods;
	    } else {
		methods 
		    = (CMethodSet.MethodArgsPair[]) Utils.combineArrays(methods, refinedMethods);
	    }
	}
	return methods;
    }

    /**
     * Returns a list of interface methods. This method is called to check
     * whether all interface methods are implemented by the class
     * being type-checked. Thus, it is refined here to return only non-model
     * methods.
     */
    public CMethodSet.MethodArgsPair[] getInterfaceMethods() {
	finishSymbolTable();
	finishSymbolTableForInterfaces();
	CMethodSet.MethodArgsPair[] methods = filterModelMethods(super.getInterfaceMethods());
	if( refinedSourceClass != null ) {
	    CMethodSet.MethodArgsPair[] refinedMethods
		= refinedSourceClass.getInterfaceMethods();
	    // no need to filter since done in the above call
	    if ( refinedMethods.length == 0 ) {
		return methods;
	    } else if ( methods.length == 0 ) {
		return refinedMethods;
	    } else {
		methods 
		    = (CMethodSet.MethodArgsPair[]) Utils.combineArrays(methods, refinedMethods);
	    }
	}
	return methods;
    }

    /**
     * Accumulates the set of methods with identifier
     * <code>name</code> declared in the type represented by this,
     * <em>or added to the type by external methods</em>, using the
     * strategy <code>actor</code>.  Only searches supertypes if no
     * matches have been accumulated while searching the type
     * represented by this.
     *
     * In this overriding method, we also accumulate methods from the
     * refined class declaration of the refines clause, but only if no
     * matches have been accumulated from this type and its
     * supertypes.
     *
     * @param	name		method name
     * @param	actor		the strategy for selecting methods
     * @param	accum		a method set in which to accumulate the 
     *				results
     * @param	context		the context in which the method reference
     *				appears, used for resolving augmenting
     * @exception UnpositionedError at the discretion of the strategy
     *                          <code>actor</code> */
    protected void accumMostSpecificMethods( String name, 
					     NoDupStrategy actor,
					     CMethodSet accum,
					     CClassType[] args,
					     CContextType context ) 
	throws UnpositionedError 
    {
	super.accumMostSpecificMethods(name, actor, accum, args ,context);

	if( accum.size() == 0 && refinedSourceClass != null ) {
	    refinedSourceClass.
		accumMostSpecificMethods(name, actor, accum, args ,context);
	}
    }

    /**
     * Filters out all model methods and returns only non-model methods.
     */
    private static CMethodSet.MethodArgsPair[] filterModelMethods(CMethodSet.MethodArgsPair[] methods) {
	if (methods.length > 0) {
	    ArrayList l = new ArrayList(methods.length);
	    for (int i = 0; i < methods.length; i++) {
		if (!hasFlag(methods[i].getMethod().access().modifiers(), ACC_MODEL)) {
		    l.add(methods[i]);
		}
	    }
	    methods = (CMethodSet.MethodArgsPair[])l.toArray
		(new CMethodSet.MethodArgsPair[l.size()]);
	    
	}
	return methods;
    }

    /** 
     *  Computes the number associated with the suffix of the given file 
     *  name.  Suffixes are grouped for the purpose of handling and checking 
     *  refinement sequences.
     *
     *  The level number is determined by the suffix of the source file.
     *  Level 8 -- ".jml-refined".
     *  Level 7 -- ".spec-refined".
     *  Level 6 -- ".java-refined".
     *  Level 5 -- ".jml".
     *  Level 4 -- ".spec".
     *  Level 3 -- ".java".
     *  Level 2 -- ".refines-jml".
     *  Level 1 -- ".refines-spec".
     *  Level 0 -- ".refines-java". 
     *
     *  The level number is used to form an ordering 
     *  of the allowable sequence of refining files.
     *
     *  That is, a file at a lower level can only refine a file at the same 
     *  or higher level, if it is the most refined definition of a class. 
     *  Also, the most refined definition of a class must be declared 
     *  in a file with the same name as the class so it will be found by 
     *  the type checker when that class is loaded.  
     */
    public static int computeSuffixNumber( String fileName ) {
	String suffix;
	int pos = fileName.lastIndexOf('.');
	if (pos < 0) {
	    // No suffix--this should not happen in general
	    return -1;
	} else {
	    suffix = fileName.substring(pos);
	}
	if ( suffix.equals(".refines-java") ) {
	    return 0;
	} else if ( suffix.equals(".refines-spec") ) {
	    return 1;
	} else if ( suffix.equals(".refines-jml") ) {
	    return 2;
	} else if ( suffix.equals(".java") ) {
	    return 3;
	} else if ( suffix.equals(".spec") ) {
	    return 4;
	} else if ( suffix.equals(".jml") ) {
	    return 5;
	} else if ( suffix.equals(".java-refined") ) {
	    return 6;
	} else if ( suffix.equals(".spec-refined") ) {
	    return 7;
	} else if ( suffix.equals(".jml-refined") ) {
	    return 8;
	} else if ( suffix.equals(".class") ) {
	    return 9;
	}
	return -1;
    }

    /**
     * Finishes pre-processing of this type so it can be used as 
     * a symbol table.
     */
    public void finishSymbolTable() {
	if( ! finishedPreProcessing ) {
	    JmlTypeLoader.getJmlSingleton()
		.activateSymbolTableBuild(this.qualifiedName());
	}
    }

    public void finishSymbolTableForInterfaces() {
	CClassType[] interfaces = getInterfaces();
	for (int i = 0; i < interfaces.length; i++) {
	    CClass nextInterface = interfaces[i].getCClass();
	    if (nextInterface instanceof JmlSourceClass) {
		((JmlSourceClass)nextInterface).finishSymbolTable();
	    }
	}
    }

    /**
     * Accumulates the set of methods with identifier
     * <code>name</code> declared in the type represented by this,
     * using the strategy <code>actor</code>.  Searches neither
     * external methods nor supertypes.
     *
     * This overriding method does, however, search refining types.
     *
     * @param	name		method name
     * @param	actor		the strategy for selecting methods
     * @param	accum		a method set in which to accumulate the 
     *				results
     * @exception UnpositionedError at the discretion of the strategy
     *                          <code>actor</code> */
    protected void accumLocalInternalMethods( String name, 
					      NoDupStrategy actor,
					      CMethodSet accum,
					      CClassType[] args)
	throws UnpositionedError 
    {
	finishSymbolTable();
	super.accumLocalInternalMethods( name, actor, accum, args );

	// check the methods of the refined type
	if (this.isRefiningType()) {
	    CMethodSet refinedMethods = new CMethodSet();
	    getRefinedType().accumLocalInternalMethods( name, actor, 
							refinedMethods,
                                                        args);

	    // We only add refinedMethods if they have not already been added;
	    // this avoids the ambiguous method error message.
	    // This is required so the overridden methods can be determined 
	    // properly when there is a refinement.
	    CAbstractMethodSet.Iterator iter = refinedMethods.iterator();
	    while (iter.hasNext()) {
		CMethod currMeth = (CMethod) iter.next();
		if( !accum.contains(currMeth) ) {
		    accum.addMethod(currMeth);
		}
	    }
	}
    }

    /**
     * For looking up methods that are not overloaded and appear 
     * in JML clauses that list method calls.
     */
    public CMethodSet lookupJMLMethodName( final String name,
					   final CContextType context )  
        throws UnpositionedError 
    {

	NoDupStrategy actor = 
	    new NoDupStrategy() {
		    public boolean maybeInclude( CMethod candidate,
						 CClassType[] args) 
			throws UnpositionedError
		    {
			if( !name.equals( candidate.ident() ) ) {
			    return false;
			}
			return true;
		    }

		    public byte resultFor( CMethod candidate,
					   CMethod accumMethod )
			throws UnpositionedError
		    {
			boolean ignoreCurrent = false;
			boolean done = false;
			boolean remove = false;
			return CMethodSet.makeResult( ignoreCurrent, remove, 
						      done );
		    }
		};

	// lookup in the methods 
	JmlSourceClass currType = this;
	CMethodSet result = new CMethodSet();
	try {
	    accumLocalExtAndInheritedMethods( name, actor, 
					      result, 
					      getType().getArguments(),
					      context );
	} catch (UnpositionedError e) {
	    // shouldn't happen
	}
	
	return result;
    }

    /**
     * Searches for the method refined by a given method, 
     * looking in the refinement hierarchy as needed.
     *
     * @param	specMethod	the method that is doing the specializing
     * @return	The method refined by <code>specMethod</code>, 
     *		or null if it does not <em>refine</em> a method declared in 
     *          a type refined by this type.  
     * @exception UnpositionedError -- should not happen
     */
    public JmlSourceMethod lookupRefinedMethod( final CMethod specMethod )
    {
	final String methName = specMethod.ident();

	// accum satisfies the invariants that <code>specMethod</code>
	// refines all methods in accum and they all  
	// have the same signature. 

	NoDupStrategy actor = 
	    new NoDupStrategy() {
		    public boolean maybeInclude( CMethod candidate,
						 CClassType[] args) 
			throws UnpositionedError
		    {
			if( specMethod == candidate ) {
			    return true;
			}
			if( !methName.equals( candidate.ident() ) ) {
			    return false;
			}
			if( !specMethod.equalParameters( candidate ) ) {
			    return false;
			}
			return true;
		    }

		    public byte resultFor( CMethod candidate,
					   CMethod accumMethod )
			throws UnpositionedError
		    {
			boolean ignoreCurrent = false;
			boolean done = false;
			boolean remove = false;
			return CMethodSet.makeResult( ignoreCurrent, remove, 
						      done );
		    }
		};

	// lookup in the methods of the refined type
	JmlSourceMethod refinedMeth = null;
	JmlSourceClass currType = this;
	CMethodSet refinedMethodSet = new CMethodSet();
	while (currType.isRefiningType()) {
	    currType = currType.getRefinedType();
	    try {
		currType.accumLocalInternalMethods(methName, actor, 
						   refinedMethodSet,
                                                   getType().getArguments());
	    } catch (UnpositionedError e) {
		// shouldn't happen
	    }
	    if (! refinedMethodSet.isEmpty()) {
		refinedMeth = (JmlSourceMethod) refinedMethodSet.getFirst();
		break;
	    }
	}
	
	return refinedMeth;
    }

    /**
     * Searches for the field refined by a given field, 
     * looking in the refinement hierarchy as needed.
     *
     * @param	specField	the refining field 
     * @return	The field refined by <code>specField</code>, 
     *		or null if it does not refine a field declared in 
     *          a type refined by this type.  
     */
    public JmlSourceField lookupRefinedField( final CField specField )
    {
	final String name = specField.ident();

	// lookup in the class of the refined type
	CField field = null;
	if (refinedSourceClass != null) {
	    field = refinedSourceClass.getDeclaredField(name);
	}

	return (JmlSourceField) field;
    }

    /**
     * Searches for the inner type refined by a given inner type, 
     * looking in the refinement hierarchy as needed.
     *
     * @param	specType	the refining inner type 
     * @return	The inner type refined by <code>specType</code>, 
     *		or null if it does not refine an inner type declared in 
     *          a type refined by this type.  
     */
    public JmlSourceClass lookupRefinedInnerType( final CClass specType )
    {
	final String name = specType.ident();

	// lookup in the refined type
	CClass innerType = null;
	if (refinedSourceClass != null) {
	    innerType = refinedSourceClass.getDeclaredInnerType(name);
	}

	return (JmlSourceClass) innerType;
    }

    /** 
     *  Searches for the inner type with the given name. 
     * 
     *  If not found in this class object, continue looking in any 
     *  refined JmlSourceClass objects.
     */
    protected CClass getDeclaredInnerType( String name ) 
    {
	// Important!  Must use inners from typeAST in order to get 
	// the proper CClass. 
	ArrayList inners = new ArrayList(typeAST.inners());
	Iterator iter = inners.iterator();
	CClass innerType = null;
	while (iter.hasNext()) {
	    JmlMemberDeclaration innerDecl = (JmlMemberDeclaration) iter.next();
	    CClass maybeResult = innerDecl.getCClass();
	    if( maybeResult.ident().equals(name) ) {
		innerType = maybeResult;
		break;
	    }
	}
	

	if (innerType == null && refinedSourceClass != null) {
	    innerType = refinedSourceClass.getDeclaredInnerType(name);
	}
	return innerType;
    }

    /**
     * Accumulates the set of methods with identifier
     * <code>name</code> declared in the type represented by this,
     * <em>ignoring external methods</em>, using the strategy
     * <code>actor</code>.  <em>Always</em> searches supertypes,
     * <em>but only those parsed by the JML parser</em>.
     *
     * @param	name		method name
     * @param	actor		the strategy for selecting methods
     * @param	accum		a method set in which to accumulate the 
     *				results, satisfying the invariant that
     *				all methods in accum are applicable to 
     *				the other arguments and any two distinct
     *				methods in accum are incomparable by the
     *				specializes relationship
     * @exception UnpositionedError at the discretion of the strategy
     *                          <code>actor</code> */
    private void accumMethodsJMLOnly( NoDupStrategy actor,
					String name,
					CMethodSet accum )
    {
	if (actor.alreadySearched(this))
	    return;

	// check the regular methods of this class
	try {
	    accumLocalInternalMethods( name, actor, accum, getType().getArguments() );
	} catch (UnpositionedError e) {
	    // shouldn't happen
	}

	CClass superClass = getSuperClass();
	// check the methods of the superclass
	if (superClass instanceof JmlSourceClass) {
	    ((JmlSourceClass)superClass)
		.accumMethodsJMLOnly( actor, name, accum );
	}

	CClassType[] interfaces = getInterfaces();
	for (int i = 0; i < interfaces.length; i++) {
	    CClass nextInterface = interfaces[i].getCClass();
	    if (nextInterface instanceof JmlSourceClass) {
		((JmlSourceClass)nextInterface)
		    .accumMethodsJMLOnly( actor, name, accum );
	    }
	}
    }


    /**
     * Searches for the methods with the same signature as the given method, 
     * looking in parent hierarchy as needed.
     *
     * @param	specMethod	the method that is doing the overriding
     * @return	A set of methods, all with the same static type tuple and 
     *		ident as <code>specMethod</code>, such that 
     *		<code>specMethod</code> <em>immediately specializes</em> 
     *		each method in the set.
     */
    /*package*/ CMethodSet lookupJMLMethodsWithSameSig( final CMethod specMethod ) 
    {
	final String name = specMethod.ident();
	CMethodSet accum = new CMethodSet();

	NoDupStrategy actor = 
	    new NoDupStrategy() {
		    public boolean maybeInclude( CMethod candidate,
						 CClassType[] args) 
		    {
			if( specMethod == candidate ) {
			    return true;
			}
			if( !name.equals( candidate.ident() ) ) {
			    return false;
			}
			if( !specMethod.equalParameters( candidate ) ) {
			    return false;
			}
			if (! (candidate instanceof JmlSourceMethod) ) {
			    return false;
			}
			return true;
		    }

		    public byte resultFor( CMethod candidate,
					   CMethod accumMethod )
		    {
			boolean ignoreCurrent = false;
			boolean done = false;
			boolean remove = false;
			return CMethodSet.makeResult( ignoreCurrent, remove, 
						      done );

		    }
		};

	accumMethodsJMLOnly( actor, name, accum );
	
	return accum;
    }

    // ----------------------------------------------------------------------
    // ACCESS methods
    // ----------------------------------------------------------------------

    /**
     * @return	the member access information object for this member.
     */
    public /*@ pure @*/ JmlMemberAccess jmlAccess() {
        return (JmlMemberAccess) access();
    }

    /**
     * Returns true if this member is declared in a '.java' file.
     */
    public /*@ pure @*/ boolean inJavaFile() {
	return levelNumber == 3;
    }

    /**
     * Returns true if this member is declared in a '.spec' file.
     */
    public /*@ pure @*/ boolean inSpecFile() {
	return levelNumber == 4;
    }

    /**
     * Returns true if this member has finished the pre-processing 
     * needed so it can be used as a symbol table, i.e., the 
     * type has been processed through the checkInitializer phase.
     */
    public /*@ pure @*/ boolean isFinishedPreProcessing() {
	return finishedPreProcessing;
    }

    /**
     * Sets the flag to true that this member has finished the pre-processing 
     * needed so it can be used as a symbol table, i.e., the 
     * type has been processed through the checkInitializer phase.
     */
    public void setFinishedPreProcessing() {
	this.finishedPreProcessing = true;
	// System.out.println("finished symtab:"+qualifiedName()+"."+levelNumber);
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Creates an instance of <code>ClassInfo</code>. This method is
     * overridden here to return an instnace of the class JmlClassInfo.
     */
    protected ClassInfo createClassInfo(long modifiers,
                                        String superClass,
                                        File sourceFile) {
        return new JmlClassInfo(modifiers,
                                qualifiedName(),
                                superClass,
                                genInterfaces(),
                                genFields(),
                                genMethods(),
                                genInners(),
                                genCustomAttributes(),
                                sourceFile,
                                false);
    }

    /**
     * Returns an array representing all the fields for bytecode. This
     * method is overridden here to return field infos for combined
     * fields through the refinement chain.
     */
    protected FieldInfo[] genFields() {
        if (typeAST == null) {
            return super.genFields();
        }
        
        // get all fields from refined types.
        JFieldDeclarationType[] fields = 
            ((JmlTypeDeclaration)typeAST).getCombinedFields();
        CField[] cfields = new CField[fields.length];
        for (int i = 0; i < cfields.length; i++) {
            cfields[i] = fields[i].getField();
        }
        CFieldTable ftable = new CFieldTable(cfields, null);
        return ftable.buildFieldInfo();
    }

    /**
     * Returns an array representing all the methods for
     * bytecode. This method is overridden here to return method infos
     * for combined methods through the refinement chain.
     */
    protected MethodInfo[] genMethods() {
        if (typeAST == null) {
            return super.genMethods();
        }

        // get all methods from refined types.
        JmlMemberDeclaration[] methods = 
            ((JmlTypeDeclaration)typeAST).getCombinedMethods();
        CMethod[] cmethods = new CMethod[methods.length];
        for (int i = 0; i < cmethods.length; i++) {
            cmethods[i] = ((JmlMethodDeclaration)methods[i]).getMethod();
        }
	return new CMethodSet(cmethods).buildMethodInfo();
    }


    /**
     * Collects all the inner classes that must be added to the
     * InnerClasses attribute. This method is overridden here to
     * combine inner classes through the refinement chain.
     * Refer to the method <code>genInners</code>.
     */
    protected CClassType[] innerClassesForAttribute() {
        if (typeAST == null) {
            return super.innerClassesForAttribute();
        }

        JmlMemberDeclaration[] cdecls = 
            ((JmlTypeDeclaration)typeAST).getCombinedInners();
        CClassType[] inners = new CClassType[cdecls.length];
        for (int i = 0; i < inners.length; i++) {
            inners[i] = ((JmlTypeDeclaration)cdecls[i]).getCClass().getType();
        }
        return inners;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** 
     *  The level number is determined by the suffix of the source file.
     *  Level 9 -- ".class".
     *  Level 8 -- ".jml-refined".
     *  Level 7 -- ".spec-refined".
     *  Level 6 -- ".java-refined".
     *  Level 5 -- ".jml".
     *  Level 4 -- ".spec".
     *  Level 3 -- ".java".
     *  Level 2 -- ".refines-jml".
     *  Level 1 -- ".refines-spec".
     *  Level 0 -- ".refines-java". 
     *
     *  The level number is used to form an ordering 
     *  of the allowable sequence of refining files.
     *
     *  That is, if a file is the most refined definition of a class,
     *  then it can only refine a file at the same or higher level. 
     *  Also, the most refined definition of a class must be declared 
     *  in a file with the same name as the class so it will be found by 
     *  the type checker when that class is loaded.  
     */
    protected int levelNumber = -1;

    private static CField modelField = null;
    private static int stackLevel = 0;

    /**
     *  This field contains the source class of the type declaration 
     *  that is refined by the current type; it is used when looking 
     *  up names such as fields or classes.  This is only done 
     *  when looking for a name referenced inside a specification.  
     */
    protected JmlSourceClass refinedSourceClass = null;

    protected JmlSourceClass refiningSourceClass = null;

    private JmlMemberDeclaration typeAST = null;

    private boolean finishedPreProcessing = false;
}
