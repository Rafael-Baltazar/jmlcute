/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, the type checker for the Java Modeling Language.
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
 * $Id: JmlCompilationUnitContext.java,v 1.18 2005/12/23 17:07:46 chalin Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CBinaryClass;
import org.multijava.mjc.CBinaryClassContext;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CCompilationUnitContext;
import org.multijava.mjc.CCompilationUnitContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CType;
import org.multijava.mjc.CVariableState;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.MJMathMode;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents the context for a compilation unit during checking
 * passes (checkInterface, checkInitializers, typecheck).
 * @see CContextType
 */
public class JmlCompilationUnitContext extends JmlContext
    implements CCompilationUnitContextType, Constants
{
    
    //@ invariant delegee instanceof CCompilationUnitContext;

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a compilation unit context.
     *
     * <pre><jml>
     * requires compiler != null && cunit != null;
     * ensures delegee != null && (delegee instanceof CCompilationUnitContext);
     * </jml></pre>
     */
    JmlCompilationUnitContext(org.multijava.mjc.Main compiler, CCompilationUnit cunit) {
	delegee = new CCompilationUnitContext(compiler, cunit);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (INFOS)
    // ----------------------------------------------------------------------

    /**
     * Fields cannot be declared in the context of a compilation unit
     * (yet), consequently we do not expect to invoke this method on a
     * compilation unit context.
     *
     * @exception	UnsupportedOperationException
     */
    public CVariableState fieldInfo(int pos) {
	throw new UnsupportedOperationException();
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
    public CClass lookupClass(String name) throws UnpositionedError {
	return delegee.lookupClass(name);
    }

     /**
     * Searches for the most specific method applicable to the given
     * identifier and argument type tuple, in the current context.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @param	context		the context of the class containing
     * 				the method call
     * @exception UnpositionedError if the result is ambiguous */
    public CMethod lookupMethod( String name, CType[] params,
				 CClassContextType context ) 
	throws UnpositionedError 
    {
	return null;
    }

     /**
     * Searches for the most specific method(s) applicable to the given
     * identifier and argument type tuple, in the current context.
     *
     * @param	name		method name
     * @param	params		method parameter types
     * @param	context		the context of the class containing
     * 				the method call
     * @exception UnpositionedError if the result is ambiguous */
    public CMethodSet lookupMethodOrSet( String name, CType[] params,
					 CClassContextType context ) 
	throws UnpositionedError 
    {
	return null;
    }

   /**
     * searches for a field with the given identifier
     * @return a field from an ident in current context
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public CFieldAccessor lookupField(String ident,
				      CExpressionContextType context)
	throws UnpositionedError {
	return null;
    }

    /**
     * Finds the variable with the given identifier in this context.
     * @param	ident		the name of the local variable
     * @return	a variable from an ident in current context
     */
    public JLocalVariable lookupLocalVariable(String ident) {
	return null;
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
    public JExpression lookupOuterLocalVariable( TokenReference ref, 
						 String ident ) {
	return null;
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
    public CFieldAccessor lookupOuterField(String ident,
					   CExpressionContextType context)
	throws UnpositionedError {
	return null;
    }

    /**
     * Searches for any imported external generic functions.
     *
     * @param	ident	the name of the generic function to search for
     */
    public void resolveMaybeExtMethodRef(String ident) {
	delegee.resolveMaybeExtMethodRef(ident);
    }

    /**
     * Registers that a declaration of the given method occurs within
     * the compilation unit. */
    public void registerVisibleMethod(CMethod method) {
	delegee.registerVisibleMethod(method);
    }

    /**
     * Registers that a reference to the given type occurs within
     * the compilation unit. */
    public void registerVisibleType(CType type) {
	delegee.registerVisibleType(type);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (TREE HIERARCHY)
    // ----------------------------------------------------------------------

    /**
     * getParentContext
     * @return	the parent
     */
    public CContextType getParentContext() {
	fail();
	return null;
    }

    /**
     * getClass
     * @return	the near parent of type CClassContextType
     */
    public CClassContextType getClassContext() {
	return null;
    }

    /**
     * getMethod
     * @return	the near parent of type CMethodContextType
     */
    public CMethodContextType getMethodContext() {
	return null;
    }

    /**
     * @return	the compilation unit
     */
    public CCompilationUnitContextType getCompilationUnit() {
	return this;
    }

    /** 
     * Returns the nearest control flow context (where control flow
     * information is stored.)
     * @return the nearest parent of type CFlowControlContextType
     */
    public CFlowControlContextType getFlowControlContext() {
	return null;
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
     * <code>CMemberHost</code>, i.e., <code>this.cunit</code> */
    public CMemberHost findNearestHost() {
	return delegee.findNearestHost();
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (NEW CONTEXT)
    // ----------------------------------------------------------------------

    public CBinaryClassContext createBinaryClassContext(CBinaryClass clazz) {
	// !FIXME! return JmlBinaryClassContext
	//return new CBinaryClassContext( this, clazz );
	return ((CCompilationUnitContext)delegee).createBinaryClassContext(clazz);
    }

    // ----------------------------------------------------------------------
    // ERROR HANDLING
    // ----------------------------------------------------------------------

    /**
     * Adds a trouble into the list and eats it. This method should be
     * called after a try catch block after catching exception or
     * directly without exception thrown.o
     * @param trouble the trouble
     */
    public void reportTrouble(Exception trouble) {
	delegee.reportTrouble(trouble);
    }

    /**
     * Gets the compiler
     */
    public org.multijava.mjc.Main getCompiler() {
	return delegee.getCompiler();
    }
  
    // ----------------------------------------------------------------------
    // CLASS HANDLING
    // ----------------------------------------------------------------------

    /**
     * Adds a class to generate
     */
    public void classToGenerate( CSourceClass clazz ) {
	delegee.classToGenerate(clazz);
    }

    /**
     * Indicates whether this is equal to a given object.
     *
     * @param	o		the object to compare against
     * @return	true iff <code>o</code> is another 
     *		<code>CCompilationUnitContextType</code> formed around an
     *		identical (i.e., <code>==</code>) <code>CCompilationUnit</code>
     */
    public boolean equals(/*@ nullable @*/  Object o ) {
	return (o instanceof JmlCompilationUnitContext)
	    && delegee.equals( ((JmlCompilationUnitContext) o).delegee);
    }

    /**
     * Returns the hash code for this, equivalent to 
     * <code>this.cunit.hashCode()</code>.
     *
     * @return	the hash code for this
     */
    public int hashCode() {
	return delegee.hashCode();
    }

    public Main.PTMode mode() { return mode; }

    public void setMode(Main.PTMode m) { mode = m; }

    // -------------------------------------------------------------
    // UTILITY METHODS
    // -------------------------------------------------------------
  
    public MJMathMode arithmeticMode() {
    	if(getCompiler().safeMath()){
    		//return Constants.AMID_SAFE_MATH;
    		return MJMathMode.newMJMathMode(Constants.AMID_SAFE_MATH);
    	}
	//return Constants.AMID_JAVA_MATH;
	return super.arithmeticMode();
    }

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    private Main.PTMode mode;
}
