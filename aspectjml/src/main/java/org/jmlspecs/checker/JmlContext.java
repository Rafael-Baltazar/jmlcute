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
 * $Id: JmlContext.java,v 1.35 2006/12/13 21:09:05 wdietl Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContext;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CCompilationUnitContext;
import org.multijava.mjc.CCompilationUnitContextType;
import org.multijava.mjc.CConstructorContextType;
import org.multijava.mjc.CContext;
import org.multijava.mjc.CContextNullity;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CExtMethodContext;
import org.multijava.mjc.CField;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFlowControlContext;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CGenericFunctionCollection;
import org.multijava.mjc.CInterfaceContextType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodContext;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.CVariableInfoTable;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JPhylum;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MJMathMode;
import org.multijava.mjc.VariableDescriptor;
import org.multijava.util.MessageDescription;
import org.multijava.util.Utils;
import org.multijava.util.compiler.ModifierUtility;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * <p>Descendents of this class represent local contexts during
 * checking passes (checkInterface, checkInitializers, typecheck).
 * The context classes follow the control flow and maintain
 * information about variables (initialized, used, allocated) and
 * exceptions (thrown, caught).  They also verify that a context is
 * still reachable.  The contexts are used for name resolution (JLS2,
 * 6 and 14.4), checking for unreachable statements (JLS2 14.20),
 * checking for definite assignment (JLS2, 16), and for checking for
 * proper subclassing and overriding (JLS2, 8).</p>
 *
 * <p>The contexts are hierarchical. To wit, a compilation unit context
 * is created and passed to the method that checks a class.  This
 * method creates a class context by passing the compilation unit
 * context to the CClassContext constructor.  When checking methods of
 * the class the CClassContext instance is passed to the CMethodContext
 * constructor.  These context classes are stored in fields of the AST
 * nodes.</P>
 *
 * <P>During typechecking the context hierarchy is mutated in a way
 * that mimics the actual run-time control flow.  For example,
 * variable declarations cause the context to be mutated to record the
 * variable's name and type.  Assignment to a variable causes the
 * context to be mutated to record that the variable is definitely
 * assigned.  Reference a variable's value triggers a check that the
 * variable has been definitely assigned.</P>
 *
 * */
public abstract class JmlContext extends Utils 
    implements CContextType, Constants 
{
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new context.
     */
    JmlContext() {
	cunit = (CCompilationUnitContextType)this;
    }

    /**
     * Construct a block context, it supports local variable allocation
     * throw statement and return statement
     * @param	parent		the parent context, it must be different
     *				than null except if called by the top level
     */
    protected JmlContext(/*@non_null*/ CContextType parent) {
	this.parent = parent;
	cunit = parent.getCompilationUnit();

	// for rationale of the following 2 lines,
	// see comment in CContext's constructor
	addFANonNulls(parent.getFANonNulls());
	addFANulls(parent.getFANulls());
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (LOOKUP)
    // ----------------------------------------------------------------------

    /**
     * Searches for a class with the given simple name according the procedure
     * in JLS2 6.5.5.
     * 
     * @param	name	the class name, without qualifiers
     * @return	the class if found, null otherwise
     * @exception	UnpositionedError	if search fails
     */
    public /*@nullable*/ CClass lookupClass(/*@non_null@*/ String name) throws UnpositionedError {
	return parent.lookupClass(name);
    }

    public /*@nullable*/ CTypeVariable lookupTypeVariable(/*@non_null@*/ String ident) throws UnpositionedError {
        return (parent == null) ? null : parent.lookupTypeVariable(ident);
    }

    /**
     * Searches for the most specific method in the current context
     * that is applicable to the given identifier and argument type
     * tuple.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @exception UnpositionedError if the result is ambiguous */
    public /*@nullable*/ CMethod lookupMethod(/*@non_null@*/  String name, CType[] params ) 
	throws UnpositionedError 
    {
	return lookupMethod( name, params, getClassContext() );
    }

    /**
     * Searches for the most specific method in the current context
     * that is applicable to the given identifier and argument type
     * tuple.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @param	context		the context of the class containing
     * 				the method call
     * @exception UnpositionedError if the result is ambiguous */
    public /*@nullable*/ CMethod lookupMethod(/*@non_null@*/ String name, CType[] params,
				/*@non_null@*/ CClassContextType context ) 
	throws UnpositionedError 
    {
	return parent.lookupMethod( name, params, context );
    }

    /**
     * Searches for the most specific method(s) in the current context
     * that is applicable to the given identifier and argument type
     * tuple.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @exception UnpositionedError if the result is ambiguous */
    public /*@nullable*/ CMethodSet lookupMethodOrSet(/*@non_null@*/ String name, CType[] params ) 
	throws UnpositionedError 
    {
	return lookupMethodOrSet( name, params, getClassContext() );
    }

    /**
     * Searches for the most specific method(s) in the current context
     * that is applicable to the given identifier and argument type
     * tuple.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @param	context		the context of the class containing
     * 				the method call
     * @exception UnpositionedError if the result is ambiguous */
    public /*@nullable*/ CMethodSet lookupMethodOrSet(/*@non_null@*/ String name, CType[] params,
					/*@non_null@*/ CClassContextType context ) 
	throws UnpositionedError 
    {
	return parent.lookupMethodOrSet( name, params, context );
    }

    /**
     * searches for a field with the given identifier
     * @return a field from an ident in current context
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public /*@nullable*/ CFieldAccessor lookupField(/*@non_null@*/ String ident) throws UnpositionedError {
	return parent.lookupField(ident);
    }

    /**
     * searches for a field with the given identifier
     * @return a field from an ident in current context
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public /*@nullable*/ CFieldAccessor lookupField(/*@non_null@*/ String ident,
				      /*@non_null@*/ CExpressionContextType context)
	throws UnpositionedError {
	return parent.lookupField(ident, context);
    }

    /**
     * searches for a local variable with the given identifier
     * @param	ident		the name of the local variable
     * @return	a variable from an ident in current context
     */
    public /*@nullable*/ JLocalVariable lookupLocalVariable(/*@non_null@*/ String ident) {
	return parent.lookupLocalVariable(ident);
    }

    /**
     * Finds a local variable with the given name that appears outside
     * the current lexical contour.
     *
     * @param	ref		a token reference used to build a new
     *				<code>JOuterLocalVariableExpression</code>
     * @param	ident		the name of the outer variable
     * @return a variable from an ident in the surrounding context, or null
     *		if not found */
    public /*@nullable*/ JExpression lookupOuterLocalVariable(/*@non_null@*/ TokenReference ref, 
						/*@non_null@*/ String ident ) {
	return parent.lookupOuterLocalVariable( ref, ident );
    }

    /**
     * Searches for a field of the given name in the context surrounding the
     * current lexical contour.
     *
     * @param	ident		the name of the field
     * @return	a variable from a field in the surrounding context, or null
     *		if none is found
     * @exception UnpositionedError	this error will be positioned soon
     */
    public /*@nullable*/ CFieldAccessor lookupOuterField(/*@non_null@*/ String ident)
	throws UnpositionedError {
	return parent.lookupOuterField( ident );
    }

    /**
     * Searches for a field of the given name in the context surrounding the
     * current lexical contour.
     *
     * @param	ident		the name of the field
     * @param	context		the context of the field access
     * @return	a variable from a field in the surrounding context, or null
     *		if none is found
     * @exception UnpositionedError	this error will be positioned soon
     */
    public /*@nullable*/ CFieldAccessor lookupOuterField(/*@non_null@*/ String ident,
					   /*@non_null@*/ CExpressionContextType context)
	throws UnpositionedError {
	return parent.lookupOuterField( ident, context );
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (INFOS)
    // ----------------------------------------------------------------------

    /**
     * Replaces the local field info for fields in positions 0 up to
     * <code>pos</code> with the info in <code>replacement</code>.  */
    public void replaceFieldInfoUpTo( int pos, 
				      CVariableInfoTable replacement ) {
	parent.replaceFieldInfoUpTo( pos, replacement );
    }

    /**
     * Marks the field with the given descriptor as definitely assigned
     * to in this context.  */
    public void initializeField(VariableDescriptor varDesc) {
	parent.initializeField(varDesc);
    }

    /**
     * Indicates whether the field in the given position is
     * definitely assigned to in this context.  */
    public boolean isFieldDefinitelyAssigned(int pos) {
	return parent.isFieldDefinitelyAssigned(pos);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (TREE HIERARCHY)
    // ----------------------------------------------------------------------

    /**
     * Returns the parent context for this context
     * @return	the parent
     */
    public /*@ pure non_null @*/ CContextType getParentContext() {
	return parent;
    }

    /**
     * Returns the compilation unit context for this context.  This
     * only makes sense for contexts that do not themselves represent
     * compilation units.  I.e., in classes that represent compilation
     * unit context this should be overridden.
     * @return the compilation unit 
     */
    public /*@ pure non_null @*/ CCompilationUnitContextType getCompilationUnit() {
	return cunit;
    }

    /**
     * Returns the class context for this context.  This only makes
     * sense for contexts that can appear inside classes.  I.e., This
     * should be overridden in classes representing other sorts of contexts.
     * @return the nearest parent of type CClassContextType.
     */
    public /*@ pure non_null @*/ CClassContextType getClassContext() {
	return parent.getClassContext();
    }

    /**
     * Returns the method context for this context.  This only makes
     * sense for contexts that can appear inside methods.  I.e., This
     * should be overridden in classes representing other sorts of contexts.
     * @return	the nearest parent of type CMethodContextType.
     */
    public /*@ pure non_null @*/ CMethodContextType getMethodContext() {
	return parent.getMethodContext();
    }

    /** 
     * Returns the nearest control flow context (where control flow
     * information is stored.)
     * @return the nearest parent of type CFlowControlContextType
     */
    public /*@ pure non_null @*/ CFlowControlContextType getFlowControlContext() {
	return parent.getFlowControlContext();
    }

    /**
     * Returns the signature of the method declaration in which this
     * context is enclosed, or null if this context is not enclosed in
     * a method declaration.  */
    public /*@ pure @*/ CMethod getCMethod() {
	CMethodContextType methodContext = getMethodContext();
	return methodContext == null ? null : methodContext.getCMethod();
    }

    /**
     * Returns the signature of the class declaration in which this
     * context is enclosed, or null if this context is not enclosed in
     * a class declaration.  */
    public /*@ pure @*/ CClass getHostClass() {
	CClassContextType classContext = getClassContext();
	return classContext == null ? null : classContext.getHostClass();
    }

    /**
     * Returns the signature of the nearest lexically enclosing
     * context that can host member declarations (i.e., a
     * <code>CClass</code> or a <code>CCompilationUnit</code>).  Used
     * for access checks, this is slightly different than
     * <code>getHostClass()</code>.  The later method returns an
     * anchor class signature for external methods, which is useful in
     * code generation and in typechecking external method bodies.  On
     * the other hand, this method returns a
     * <code>CCompilationUnit</code> for external methods, which is
     * useful in checking access between two differently named generic
     * functions declared in the same compilation unit.  !FIXME! It
     * may be possible to eliminate this method and just use
     * <code>getHostClass</code> now that private external methods are
     * duplciated in every anchor.
     *
     * @return	the nearest parent that can be coerced to a 
     * <code>CMemberHost</code> */
    public /*@ pure @*/ CMemberHost findNearestHost() {
	return parent.findNearestHost();
    }


    /**
     * Creates a class context with this context as its parent.
     * @param	self		the corresponding class
     */
    public CClassContextType createClassContext( /*@non_null@*/ CClass self ) {
	return new JmlClassContext( this, self );
    }

    /**
     * Creates an interface context with this context as its parent.
     * @param	self		the corresponding interface signature
     */
    public CInterfaceContextType createInterfaceContext( /*@non_null@*/ CClass self ) {
	return new JmlInterfaceContext( this, self );
    }


    /**
     * Create a new child of this context representing the context in
     * which an external method declaration is typechecked. 
     * @param	host		the host class
     * @param	owner		the receiver class
     */
    public CExtMethodContext createExtMethodContext( /*@non_null@*/ CSourceClass host,
						     /*@non_null@*/ CClass owner ) {
	// !FIXME! eventuall return JmlExtMethodContext.
	return new CExtMethodContext( this, host, owner );
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (NULLITY)
    // ----------------------------------------------------------------------

    protected /*@non_null*/ CContextNullity getContextNullity() {
       return contextNullity;
    }
  
    /**
     * Indicates whether expr (or member) is conditionally NonNull is this context.
     */
    public /*@pure*/ boolean isFANonNull(/*@non_null*/ Object expr) {
       if (expr instanceof CFieldAccessor) 
	  return getContextNullity().isFANonNull(((CFieldAccessor)expr).getField());
       else if (expr instanceof CField) 
	  return getContextNullity().isFANonNull((CField)expr);
       else
          return getContextNullity().isFANonNull((JPhylum)expr);
    }
 
    /**
     * returns the JPhyla that are known to be non-null in this context.
     */
     public /*@pure non_null*/ Object[] getFANonNulls() {
       return getContextNullity().getFANonNulls();
     }
     public /*@pure non_null*/ Object[] getFANulls() {
       return getContextNullity().getFANulls();
     }
    /**
     * Mark expr (or member) as NonNull in this context
     */
    public void addFANonNull(/*@non_null*/ Object expr) {
       getContextNullity().addFANonNull(expr);
    }
    public void addFANull(/*@non_null*/ Object expr) {
       getContextNullity().addFANull(expr);
    }
    public void removeFANonNull(/*@non_null*/ Object expr) {
       getContextNullity().removeFANonNull(expr);
    }
    public void removeAllFANullity() {
       getContextNullity().removeAllFANullity();
    }
    /**
     * adds exprs (or members) as NonNull in this context
     */
    public void addFANonNulls(/*@non_null*/ Object[] exprs) {
       getContextNullity().addFANonNulls(exprs);
    }
    public void addFANulls(/*@non_null*/ Object[] exprs) {
       getContextNullity().addFANulls(exprs);
    }
    /**
     * Merge the list of guarded nulls in this context with that 
     * of the given context.
     * This can be done by taking a union of the two sets. 
     */
    public void mergeNullityInfo(/*@non_null*/ CContextType other) {
       getContextNullity().mergeNullityInfo(other);
    }
    public void adoptNullityInfo(/*@non_null*/ CContextType other) {
       getContextNullity().adoptNullityInfo(other);
    }
    public void dumpNonNulls(/*@non_null*/ String msg) {
       getContextNullity().dumpNonNulls(msg);
    }

    // ----------------------------------------------------------------------
    // CLASS AND EXTERNAL GF HANDLING
    // ----------------------------------------------------------------------

    /**
     * Adds a source class to be generated
     *
     * @param clazz	the class to be generated
     */
    public void classToGenerate(/*@non_null@*/ CSourceClass clazz) {
	getCompilationUnit().classToGenerate(clazz);
    }

    /**
     * Searches for any imported external generic functions.
     *
     * @param	ident	the name of the generic function to search for
     */
    public void resolveMaybeExtMethodRef( /*@non_null@*/ String ident ) {
        // Searching external generic functions is not supported yet
        // by .sym files. !FIXME! The following statement gives a
        // trouble as it often parses a source file even though the
        // corresponding .sym file has already been read, thus, I
        // think, producing another type object for the same type.
        if (!Main.hasOptionXsymr()) {
            parent.resolveMaybeExtMethodRef( ident );
        }
    }

    /**
     * Registers the declaration of an external generic function in
     * this context. */
    public void registerGFDecl(/*@non_null@*/ String methodIdent, 
			       CGenericFunctionCollection coll) {
	delegee.registerGFDecl(methodIdent,coll);
    }
    
    /**
     * Registers with the surrounding context that a declaration of
     * the given method occurs in this context. */
    public void registerVisibleMethod( /*@non_null@*/ CMethod method ) {
	// jump immediately to the top of the context hierarchy
	getCompilationUnit().registerVisibleMethod( method );
    }

    /**
     * Registers with the surrounding context that a reference to
     * the given type occurs in this context. */
    public void registerVisibleType( /*@non_null@*/ CType type ) {
	// Unlike with registerVisibleMethod above, we climb out of
	// the contexts one-by-one so the inner-most class context can
	// track the inner class used inside it.  These are needed for
	// code generation, particularly for the InnerClasses
	// attribute (see JVM2, 4.7.5).
	parent.registerVisibleType( type );
    }

    // ----------------------------------------------------------------------
    // ERROR HANDLING
    // ----------------------------------------------------------------------

    /**
     * Reports the given error and the "swallows" it, allowing
     * compilation to continue.  This method is used to report
     * non-fatal errors; for fatal errors the exception is just
     * thrown.
     *
     * @param trouble the error */
    public void reportTrouble(Exception trouble) {
	getCompilationUnit().reportTrouble(trouble);
    }

    /**
     * Generates an UnpositionedError with a given message.
     * @param	mess		the error message
     * @param	param1		the first message parameter
     * @param	param2		the second message parameter
     * @return	never, i.e., this method always throws an exception
     * @exception	UnpositionedError	the error exception
     */
    public void fail(MessageDescription mess, Object param1, Object param2)
	throws UnpositionedError
    {
	throw new UnpositionedError(mess, param1, param2);
    }

    public void fail(MessageDescription mess, Object params)
	throws UnpositionedError
    {
	throw new UnpositionedError(mess, params);
    }

    /**
     * Generates an UnpositionedError with a given message.
     * @param	mess		the error message
     * @param	params		the message parameters
     * @return	never, i.e., this method always throws an exception
     * @exception	UnpositionedError	the error exception
     */
    public void fail(MessageDescription mess, Object[] params)
	throws UnpositionedError
    {
	throw new UnpositionedError(mess, params);
    }

    /**
     * Verifies an expression and if false signals an error.
     * @param	expr		condition to verify
     * @param	mess		the message to be displayed
     * @return	true iff expr is true
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public boolean check(boolean expr,
			 MessageDescription mess) throws UnpositionedError {
	if (!expr) {
	    fail(mess, null, null);
	}
	return expr;
    }

    public boolean check(boolean expr,
			 MessageDescription mess,
			 Object[] params) throws UnpositionedError {
	if (!expr) {
	    fail(mess, params);
	}
	return expr;
    }

    /**
     * Verifies an expression and if false signals an error.
     * @param	expr		condition to verify
     * @param	mess		the message to be displayed
     * @param	param1		the first parameter
     * @return	true iff expr is true
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public boolean check(boolean expr,
			 MessageDescription mess,
			 Object param1) throws UnpositionedError {
	if (!expr) {
	    fail(mess, param1, null);
	}
	return expr;
    }

    /**
     * Verifies an expression and if false signals an error.
     * @param	expr		condition to verify
     * @param	mess		the message to be displayed
     * @param	param1		the first parameter
     * @param	param2		the second parameter
     * @return	true iff expr is true
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public boolean check(boolean expr,
			 MessageDescription mess,
			 Object param1,
			 Object param2) throws UnpositionedError {
	if (!expr) {
	    fail(mess, param1, param2);
	}
	return expr;
    }


    // -------------------------------------------------------------
    // UTILITY METHODS
    // -------------------------------------------------------------

    /**
     * Gets the compiler for this context
     */
    public /*@non_null@*/ org.multijava.mjc.Main getCompiler() {
	return parent.getCompiler();
    }

    /**
     * Returns the modifier utility for this.  */
    public final /*@non_null@*/ ModifierUtility modUtil() {
	return getCompiler().modUtil();
    }

    /**
     * Indicates whether this context is enclosed in a loop. */
    public boolean isInLoop() {
	return parent != null && parent.isInLoop();
    }

    /**
     * Indicates whether this context is enclosed in a loop and the
     * given variable is declared outside the inner-most loop
     * context. */
    public boolean declaredOutsideOfLoop(JLocalVariable var) {
	return parent != null && parent.declaredOutsideOfLoop(var);
    }

    /**
     * Returns true if the given local variable is declared exactly in
     * this context, i.e., it is not declared in an outer context. */
    public boolean declares(JLocalVariable var) {
	// Local vars are only declared in flow control contexts.
	return false;
    }

    /**
     * Indicates whether this context is enclosed in an instance or
     * static initializer.  */
    public boolean isInInitializer() {
	return parent != null && parent.isInInitializer();
    }

    /**
     * Indicates whether this context is enclosed in a constructor.  */
    public boolean isInConstructor() {
	return parent != null && parent.isInConstructor();
    }

    /**
     * Indicates whether this context is enclosed in a constructor and occurs
     * before the constructor has invoked the superclass constructor.  */
    public boolean isBeforeSuperConstructorCall() {
	return isInConstructor()
	    && !(((CConstructorContextType) getMethodContext())
		 .isSuperConstructorCalled());
    }        
    
    /**
     * Indicates whether this context is "static".
     *
     * @return true iff this context is enclosed in a context for a
     * static initializer or static method.  */
    public boolean isStatic() {
	return parent != null && parent.isStatic();
    }

    /**
     * Indicates whether this context is "pure".  By WMD.
     *
     * @return true iff this context is enclosed in a pure method.
     */
    public boolean isPure() {
	return parent != null && parent.isPure();
    }

    /**
     * Calls back to the compiler for this context and requests that
     * the compiler catch-up decl to the same pass as the currently
     * active task.  */
    public void catchUp(JTypeDeclarationType decl) {
	decl.cachePassParameters(this);
	getCompiler().catchUp(decl);
    }
      
    /**
     * Indicates the integral arithmetic mode that should be used.
     */
    public /*@non_null@*/ MJMathMode arithmeticMode(){
    	if(parent != null){
    		return parent.arithmeticMode();
    	}
	else{
		return JMLMathMode.newJMLMathMode();
	}
    }

    // -------------------------------------------------------------
    // JML-SPECIFIC METHODS
    // -------------------------------------------------------------

    public static 
	CFlowControlContextType createDummyContext(JmlSourceClass self)
    {
	CFlowControlContextType dummyContext =
	    new CFlowControlContext(
		new CMethodContext(
		    new CClassContext(
		        new CCompilationUnitContext(
			    CTopLevel.getCompiler(), 
			    null),
			self ),
		    null ),
		0, null );
	return dummyContext;
    }


    /**
     * Enters a new JML specification scope.
     * @see #exitSpecScope()
     * @see #inSpecScope()
     */
    public static void enterSpecScope() {
	specScopeCounter++;
    }

    /**
     * Exits the current JML specification scope.
     * @see #enterSpecScope()
     * @see #inSpecScope()
     */
    public static void exitSpecScope() {
	specScopeCounter--;
    }

    /** Returns <code>true</code> if currently in JML specification scope.
     *
     * @see #enterSpecScope()
     * @see #exitSpecScope()
     */
    //@ pure
    public static boolean inSpecScope() {
	return specScopeCounter > 0;
    }

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    /** number of nested spec scopes */
    private static /*@ spec_public @*/ int specScopeCounter;
    
    /**
     * The parent context.
     * <pre><jml>
     * invariant parent != null ==> parent instanceof JmlContext;
     * </jml></pre>
     */
    protected CContextType parent;

    protected CCompilationUnitContextType cunit;

    protected CContext delegee;

    private final /*@non_null*/ CContextNullity contextNullity=new CContextNullity();
}
