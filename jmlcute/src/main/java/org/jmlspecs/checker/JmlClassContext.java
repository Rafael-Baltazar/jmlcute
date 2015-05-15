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
 * $Id: JmlClassContext.java,v 1.14 2006/12/20 18:50:14 wdietl Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContext;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CConstructorContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CInitializerContextType;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.CVariableInfoTable;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.VariableDescriptor;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents the context for a class during checking
 * passes (checkInterface, checkInitializers, typecheck).
 * @see org.multijava.mjc.CContextType 
 */
public class JmlClassContext extends JmlContext implements CClassContextType 
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * @param	parent		the parent context or null at top level
     * @param	self		the corresponding clazz
     */
    JmlClassContext( CContextType parent, CClass self ) {
	super(parent);
	delegee = new CClassContext(parent, self);
    }

    /**
     * Constructs a class context.
     * @param parent the parent context, it must be different than null 
     *               except if called by the top level
     */
    protected JmlClassContext(CContextType parent) {
	super(parent);
    }

    /**
     * Verifies that all final fields are initialized and all abstract
     * methods are appropriately implemented.
     *
     * @exception UnpositionedError if any checks fail */
    public void checkingComplete( JTypeDeclarationType decl,
				  CVariableInfoTable staticC,
				  CVariableInfoTable instanceC,
				  CVariableInfoTable[] constructorsC )
	throws UnpositionedError
    {
	/* We skip the call of checkingComplete if the file we are in is a spec or jml file.
	   In those files it is not required to have final fields initialized nor methods
	   implemented; currently that is all that checkingComplete does.
	   
	   Actually, it is (now) doing more: it also checks that all interface methods are
	   implemented, that if there is an abstract method, the class is abstract, and if
	   ann field renames a field of the super class.  These checks are not performed
	   for spec files.  FIXME - to fix this will require refactoring 
	   CClassContext.checkingComplete - DRC.
        */
	if (! Main.isSpecOrJmlMode(decl.getTokenReference())) {
	    ((CClassContext)delegee).checkingComplete(decl, 
						      staticC, 
						      instanceC,
						      constructorsC);
	}
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (NEW CONTEXT)
    // ----------------------------------------------------------------------

    public CMethodContextType createMethodContext(CMethod self) {
	return new JmlMethodContext(this, self);
    }

    public CConstructorContextType createConstructorContext(CMethod self) {
	return new JmlConstructorContext(this, self);
    }

    public CInitializerContextType createInitializerContext(CMethod self) {
	return new JmlInitializerContext(this, self);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Add an initializer to this context
     */
    public void addInitializer() {
	((CClassContext)delegee).addInitializer();
    }

    /**
     * Returns true if this class need initializers
     */
    public boolean hasInitializer() {
	return ((CClassContext)delegee).hasInitializer();
    }

 
    /**
     * Returns a duplicate copy of fieldInfo table.
     *
     * @return an field into table.
     */
    public CVariableInfoTable fieldInfo() {
	return ((CClassContext)delegee).fieldInfo();
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (INFOS)
    // ----------------------------------------------------------------------

    /**
     * Replaces the local field info for fields in positions 0 up to
     * <code>pos</code> with the info in <code>replacement</code>.  */
    public void replaceFieldInfoUpTo( int pos, 
					 CVariableInfoTable replacement ) {
	((CClassContext)delegee).replaceFieldInfoUpTo(pos, replacement);
    }

    /**
     * Marks the field with the given descriptor as definitely assigned
     * to in this context.  */
    public void initializeField(VariableDescriptor varDesc) {
	((CClassContext)delegee).initializeField(varDesc);
    }

    /**
     * Indicates whether the field in the given position is
     * definitely assigned to in this context.  */
    public boolean isFieldDefinitelyAssigned(int pos) {
	return isFieldDefinitelyAssigned(pos);
    }

    /**
     * Returns the current field information for the most recently
     * checked member of this context.  It then clears the field info
     * stored in this object.  The pattern of use is to pass this
     * context into a <code>typecheck</code> method.  That method mutates this
     * context to include the variable information extracted from the
     * statement being checked.  Upon return from the
     * <code>typecheck</code> the caller calls
     * <code>fieldInfoTable</code> to extract the information.  This
     * is kludgey and one wonders why the <code>typecheck</code>
     * methods doesn't just return the <code>CVariableInfoTable</code>
     * instance. !FIXME! */
    public CVariableInfoTable fieldInfoTable() {
	return ((CClassContext)delegee).fieldInfoTable();
    }

    /**
     * Sets the field information for this to match that given by
     * <code>fieldInfo</code>.  Called before typechecking
     * constructors with the argument equal to the field assignment
     * information after checking initializers.  */
    public void setFieldInfoTable(CVariableInfoTable fieldInfo) {
	((CClassContext)delegee).setFieldInfoTable(fieldInfo);
    }

    public void markAllFieldsAsInitialized() {
	((CClassContext)delegee).markAllFieldsAsInitialized();
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (LOOKUP)
    // ----------------------------------------------------------------------

    /**
     * Searches for a class with the given simple name according the
     * procedure in JLS2 6.5.5.  This method implements the second and
     * third bullet points of the procedure.  That is "Otherwise, if
     * the simple type name occurs within the scope of exactly one
     * visible member type, then the simple type name denotes that
     * member type;" and "Otherwise, if the simple type name occurs
     * within the scope of more than one visible member type, then the
     * name is ambiguous as a type name; a compile-time error occurs."
     * If the class is not found according to these constraints, then 
     * the surrounding context is called to check the remaining bullets.
     * 
     * @param	name	the class name, without qualifiers
     * @return	the class if found, null otherwise
     * @exception UnpositionedError if search fails */
    public CClass lookupClass(String name) throws UnpositionedError {
	return ((CClassContext)delegee).lookupClass(name);
    }

    public CTypeVariable lookupTypeVariable(String ident) throws UnpositionedError {
        CTypeVariable tv = getOwnerClass().lookupTypeVariable(ident);
        if (tv!=null) {
            return tv ;
        } else {
            return getParentContext().lookupTypeVariable(ident);
        }
    }

    /**
     * Searches for the most specific method <em>when no receiver is
     * explicit at the call site</em>.
     *
     * @param	ident		method name
     * @param	params		method parameters
     * @param	context		the context of the class containing
     * 		                the method call
     * @return	the method or null if not found
     * @exception UnpositionedError this error will be positioned soon */
    public CMethod lookupMethod( String ident, CType[] params,
				 CClassContextType context ) 
	throws UnpositionedError 
    {
	return ((CClassContext)delegee).lookupMethod(ident, params, context);
    }

    /**
     * Searches for the most specific method(s) <em>when no receiver is
     * explicit at the call site</em>.
     *
     * @param	ident		method name
     * @param	params		method parameters
     * @param	context		the context of the class containing
     * 		                the method call
     * @return	the method or null if not found
     * @exception UnpositionedError this error will be positioned soon */
    public CMethodSet lookupMethodOrSet( String ident, CType[] params,
					 CClassContextType context ) 
	throws UnpositionedError 
    {
	return ((CClassContext)delegee).lookupMethodOrSet(ident, params, 
							  context);
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
	throws UnpositionedError 
    {
	return ((CClassContext)delegee).lookupOuterField(ident, context);
    }

    /**
     * lookupField
     * @param	ident		the name of the field
     * @param	context		the context of the field access
     * @return	a variable from an ident in current context
     * @exception UnpositionedError	this error will be positioned soon
     */
    public CFieldAccessor lookupField(String ident,
				      CExpressionContextType context)
	throws UnpositionedError 
    {
	return ((CClassContext)delegee).lookupField( ident, context );
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
    public JExpression lookupOuterLocalVariable(TokenReference ref, 
						String ident) 
    {
	return ((CClassContext)delegee).lookupOuterLocalVariable(ref, ident);
    }

    /**
     * lookupLocalVariable
     * @param	ident		the name of the local variable
     * @return	a variable from an ident in current context
     */
    public JLocalVariable lookupLocalVariable(String ident) {
	return ((CClassContext)delegee).lookupLocalVariable(ident);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (TREE HIERARCHY)
    // ----------------------------------------------------------------------

    /**
     * getClassContext
     * @return	the near parent of type CClassContextType
     */
    public CClassContextType getClassContext() {
	return this;
    }

    /**
     * Returns the CClass representing the signature of the class
     * containing this context.
     *
     * @return	the CClass representing the signature of the class
     */
    public CClass getHostClass() {
	return ((CClassContext)delegee).getHostClass();
    }

    /**
     * Returns the CClass representing the signature of the class
     * that is the logical owner of this context.  Useful for external
     * methods where the host is the generic function anchor but the
     * owner is the method's receiver.
     *
     * @return	the CClass representing the signature of the class
     * @see org.multijava.mjc.CClassContextType#getHostClass()
     * @see org.multijava.mjc.CExtMethodContext#getHostClass()
     */
    public CClass getOwnerClass() {
	return ((CClassContext)delegee).getOwnerClass();
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
     * duplicated in every anchor.
     *
     * @return	the nearest parent that can be coerced to a 
     * <code>CMemberHost</code>, i.e., <code>this.self</code> */
    public CMemberHost findNearestHost() {
	return ((CClassContext)delegee).findNearestHost();
    }

    // ----------------------------------------------------------------------
    // CLASS AND EXTERNAL GF HANDLING
    // ----------------------------------------------------------------------

    /**
     * Searches for any imported or private external generic functions.
     *
     * @param	ident	the name of the generic function to search for
     */
    public void resolveMaybeExtMethodRef( String ident ) {
	((CClassContext)delegee).resolveMaybeExtMethodRef(ident);
    }

    /**
     * Registers with the surrounding context that a reference to
     * the given type occurs in this context. */
    public void registerVisibleType( CType type ) {
        ((CClassContext)delegee).registerVisibleType(type);
    }

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------
}
