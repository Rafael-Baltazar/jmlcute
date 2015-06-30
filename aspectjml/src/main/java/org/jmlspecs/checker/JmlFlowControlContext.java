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
 * $Id: JmlFlowControlContext.java,v 1.17 2006/11/27 15:36:47 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CContextNullity;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFlowControlContext;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CLabeledContext;
import org.multijava.mjc.CLoopContext;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CSwitchBodyContext;
import org.multijava.mjc.CThrowableInfo;
import org.multijava.mjc.CTryContext;
import org.multijava.mjc.CType;
import org.multijava.mjc.CVariableInfoTable;
import org.multijava.mjc.JLabeledStatement;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JLoopStatement;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JSwitchStatement;
import org.multijava.mjc.VariableDescriptor;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * <P>This class is used during typechecking for control flow analysis
 * that maintains local variable definite assignment (JLS2, 16),
 * throwable, and reachability information (JLS2, 14.20).</P> */
public class JmlFlowControlContext extends JmlContext 
    implements CFlowControlContextType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a nested flow control context.
     * Clients should not call this but should instead call
     * <code>CCompilationUnitContextType.createFlowControlContext</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * ensures ((CFlowControlContext)delegee).nestedFlowControlContext;
     * </jml></pre>
     *
     * @param	parent		the parent context, it must be different
     * than null except if called by the top level 
     *
     * @see #createFlowControlContext()
     *
     */
    JmlFlowControlContext(CFlowControlContextType parent, 
			  TokenReference where) 
    {
	this(parent,DEFAULT_VAR_ESTIMATE,where);
    }

    /**
     * Construct a nested flow control context.
     * Clients should not call this but should instead call
     * <code>createFlowControlContext(int)</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * ensures ((CFlowControlContext)delegee).nestedFlowControlContext;
     * </jml></pre>
     *
     * @param parent the parent context, it must be different than
     * null
     * @param varEstimate an estimate of the number of variable slots to 
     * reserve 
     *
     * @see #createFlowControlContext(int)
     */
    JmlFlowControlContext(CFlowControlContextType parent, int varEstimate,
			  TokenReference where) {
	super(parent);
	delegee = new CFlowControlContext(parent, varEstimate, where);
    }

    /**
     * Construct an outer-most flow control context.
     * Clients should not call this but should instead call
     * <code>CMethodContextType.createFlowControlContext(int)</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * ensures !((CFlowControlContext)delegee).nestedFlowControlContext;
     * </jml></pre>
     *
     * @param parent the parent context, it must be different than null
     * @param varEstimate an estimate of the number of variable slots to 
     * reserve 
     *
     * @see CMethodContextType#createFlowControlContext(int)
     */
    JmlFlowControlContext(CMethodContextType parent, int varEstimate,
			  TokenReference where) 
    {
	super( parent );
	delegee = new CFlowControlContext(parent, varEstimate, where);
    }

    /**
     * Construct an outer-most flow control context.
     * Clients should not call this but should instead call
     * <code>CMethodContextType.createFlowControlContext(int, boolean)</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * ensures !((CFlowControlContext)delegee).nestedFlowControlContext;
     * </jml></pre>
     *
     * @param parent the parent context, it must be different than null
     * @param varEstimate an estimate of the number of variable slots to 
     * reserve
     * @param isInExternalGF true if we are currently in a method of an
     * external generic function
     *
     * @see CMethodContextType#createFlowControlContext(int)
     */
    JmlFlowControlContext(CMethodContextType parent, int varEstimate,
			  boolean isInExternalGF, TokenReference where) 
    {
	super( parent );
	delegee = new CFlowControlContext(parent, varEstimate,
					  isInExternalGF, where);
    }
    
    /**
     * Used to clone this flow control context.
     *
     * @param	parent		the parent context, it must be different
     *				than null
     * @param   clone		the context whose state is to be adopted
     */
    protected JmlFlowControlContext( CFlowControlContextType parent, 
				     CFlowControlContextType clone ) {
	super(parent);
	delegee = new CFlowControlContext(parent, clone);
    }

    // -------------------------------------------------------------
    // "DESTRUCTOR"
    // -------------------------------------------------------------

    /**
     * <P>Registers that this context is no longer needed.  Passes
     * information collected by this context to the parent context.</P>
     *
     * <p>Passes this context's field information to the surrounding
     * context; passes local variable information to the surrounding
     * context if that context is one which maintains local variable
     * information.</p>
     *
     * <P>Checks that local variables are used and issues warnings if
     * not.</P> 
     *
     * <P>This should only be called on a linearly nested context!
     * !FIXME!10/26 If we refactor the context creation code as
     * planned (to lock the parent context) then this method is called
     * to unlock the parent context when we exit a linearly nested
     * context.</P> */
    public void checkingComplete() {
	((CFlowControlContext)delegee).checkingComplete();
    }

    public TokenReference getTokenReference() {
	return ((CFlowControlContext)delegee).getTokenReference();
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (NEW CONTEXT)
    // ----------------------------------------------------------------------

    // !FIXME!10/26 can we somehow lock this context until the created
    // context or contexts are closed?

    public CFlowControlContextType createFlowControlContext(TokenReference where)
    {
	CFlowControlContextType retVal = new JmlFlowControlContext(this, where);
	retVal.adoptNullityInfo(this);
        return retVal;
    }
  
    public CFlowControlContextType createFlowControlContext(int params,
							    TokenReference where)
    {
	CFlowControlContextType retVal = new JmlFlowControlContext(this, params, where);
	retVal.adoptNullityInfo(this);
        return retVal;
    }

    public CLabeledContext createLabeledContext(JLabeledStatement self) {
	//return new CLabeledContext(this, self);
	return ((CFlowControlContext)delegee).createLabeledContext(self);
    }

    public CLoopContext createLoopContext(JLoopStatement self) {
	//return new CLoopContext(this, self);
	return ((CFlowControlContext)delegee).createLoopContext(self);
    }
  
    public CSwitchBodyContext createSwitchBodyContext( JSwitchStatement stmt,
						       CType switchType ) {
	//return new CSwitchBodyContext( this, stmt, switchType );
	return ((CFlowControlContext)delegee).createSwitchBodyContext(stmt,
	   switchType);
    }

    public CTryContext createTryContext(TokenReference where) {
	//return new CTryContext(this, where);
	return ((CFlowControlContext)delegee).createTryContext(where);
    }

    public CFlowControlContextType createFinallyContext(CFlowControlContextType tryContext, TokenReference where) {
	return ((CFlowControlContext)delegee).createFinallyContext(tryContext, where);
    }

    public CExpressionContextType createExpressionContext() {
	// !FIXME! not sure of precondition context.
	return JmlExpressionContext.createPrecondition(this);
    }

    /**
     * Create a clone of this context to handle divergent paths in the
     * control flow.  */
    public CFlowControlContextType cloneContext() {
	CFlowControlContextType retVal = new JmlFlowControlContext( 
	   ((CFlowControlContext)delegee).cachedParent(), this );
	retVal.adoptNullityInfo(this);
        return retVal;
    }

    /**
     * Creates a set of child contexts for typechecking parallel
     * control flows.  After using the contexts they should be passed
     * to the <code>adoptParallelContexts</code> method of this.
     *
     * <pre><jml>
     * also
     *   requires count > 0;
     * </jml></pre>
     *
     * @see #adoptParallelContexts(CFlowControlContextType[]) */
    public CFlowControlContextType[] createParallelContexts(int count,
							    TokenReference where)
    {
	//@ assert count > 0;
	return ((CFlowControlContext)delegee).createParallelContexts(count, 
								     where);
    }

    /**
     * Adopts the information from the given contexts.
     *
     * <pre><jml>
     * also
     *   requires contexts != null && contexts.length > 0;
     * </jml></pre>
     *
     */
    public void adoptParallelContexts(CFlowControlContextType[] contexts) {
	((CFlowControlContext)delegee).adoptParallelContexts(contexts);
    }

    // -------------------------------------------------------------
    // COMBINING CONTEXTS
    // -------------------------------------------------------------

    public void merge(CFlowControlContextType context) { 
	((CFlowControlContext)delegee).merge(context);
    }

    public void adopt(CFlowControlContextType context) {
	((CFlowControlContext)delegee).adopt(context);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (VARIABLE)
    // ----------------------------------------------------------------------

    /**
     * Checks whether a local variable has a name that is fresh
     * (i.e., no other local variable in scope has the same name).
     * @param	var		the variable
     */
    public boolean isFreshVariableName(JLocalVariable var) {
	return ((CFlowControlContext)delegee).isFreshVariableName(var);
    }
	
    /**
     * Adds a local variable to this block
     * @param	var		the name of the variable
     * @exception UnpositionedError	if the variable is a redeclaration
     */
    public void addVariable(JLocalVariable var) throws UnpositionedError {
	((CFlowControlContext)delegee).addVariable(var);
    }

    /**
     * Records that the Java keyword <CODE>this</CODE> is used in this
     * block.
     */
    public void addThisVariable() {
	((CFlowControlContext)delegee).addThisVariable();
    }

    /**
     * Records that a variable slot must be reserved for a synthetic
     * <code>this</code> parameter.  Recall that <code>this</code> is
     * passed as a parameter for external methods.  */
    public void addSyntheticThisParameter() {
	((CFlowControlContext)delegee).addSyntheticThisParameter();
    }

    /**
     * Returns the number of stack positions required to store the
     * local variables encountered thus far in this context.  */
    public int localsPosition() {
	return ((CFlowControlContext)delegee).localsPosition();
    }

    public int numberOfLocalVars() {
	return ((CFlowControlContext)delegee).numberOfLocalVars();
    }

    public CVariableInfoTable variableInfo() {
	return ((CFlowControlContext)delegee).variableInfo(); 
    }

    public CVariableInfoTable fieldInfo() {
	return ((CFlowControlContext)delegee).fieldInfo();
    }

    public ArrayList localVars() {
	return ((CFlowControlContext)delegee).localVars();
    }
    
    public int parentIndex() {
	return ((CFlowControlContext)delegee).parentIndex();
    }

    public int localsIndex() {
	return ((CFlowControlContext)delegee).localsIndex();
    }

    // -------------------------------------------------------------
    // ACCESSORS (FLOW CONTROL)
    // -------------------------------------------------------------

    /**
     * Mutates the reachability status of this context.
     *
     * @param reachable indicates whether the statements in this context 
     *			are reachable after the current statement being 
     *			checked.
     */
    public final void setReachable(boolean reachable) {
	((CFlowControlContext)delegee).setReachable(reachable);
    }

    /**
     * Indicates whether the statements in this context are reachable
     * up to most recent statement that was typechecked.  (Assuming
     * that statement's typechecking code calls
     * <code>setReachable</code> appropriately.)
     *
     * @return if this context is still reachable */
    public final boolean isReachable() {
	return ((CFlowControlContext)delegee).isReachable();
    }

    /**
     * Returns the statement with the specified label.
     */
    public JLabeledStatement getLabeledStatement(String label) {
	return ((CFlowControlContext)delegee).getLabeledStatement(label);
    }

    /**
     * Returns the nearest breakable statement.
     */
    public JStatement getNearestBreakableStatement() {
	return ((CFlowControlContext)delegee).getNearestBreakableStatement();
    }

    /**
     * Returns the nearest continuable statement.
     */
    public JStatement getNearestContinuableStatement() {
	return ((CFlowControlContext)delegee).getNearestContinuableStatement();
    }

    /** 
     * Returns the nearest control flow context (where control flow
     * information is stored.)
     * @return the nearest parent of type CFlowControlContextType
     */
    public CFlowControlContextType getFlowControlContext() {
	return this;
    }  

    // ----------------------------------------------------------------------
    // ACCESSORS (INFOS)
    // ----------------------------------------------------------------------

    /**
     * Marks the variable with the given descriptor as definitely assigned
     * to in this context.  */
    public void initializeVariable(VariableDescriptor varDesc) {
	((CFlowControlContext)delegee).initializeVariable(varDesc);
    }

    /**
     * Indicates whether the variable in the given position is
     * definitely assigned to in this context.  */
    public boolean isVarDefinitelyAssigned(int pos) {
	return ((CFlowControlContext)delegee).isVarDefinitelyAssigned(pos);
    }

    /**
     * Indicates whether the variable in the given position is
     * definitely unassigned to in this context.  */
    public boolean isVarDefinitelyUnassigned(int pos) {
	return ((CFlowControlContext)delegee).isVarDefinitelyUnassigned(pos);
    }

    /**
     * Replaces the local field info for fields in positions 0 up to
     * <code>pos</code> with the info in <code>replacement</code>.  */
    public void replaceFieldInfoUpTo( int pos, 
				      CVariableInfoTable replacement ) {
	((CFlowControlContext)delegee).replaceFieldInfoUpTo(pos,
							    replacement);
    }

    /**
     * Replaces the local variable info in positions 0 up to
     * <code>pos</code> with the info in <code>replacement</code>.  */
    public void replaceVariableInfoUpTo( int pos, 
					 CVariableInfoTable replacement ) {
	((CFlowControlContext)delegee).replaceVariableInfoUpTo(pos,
							       replacement);
    }

    /**
     * Marks the field with the given descriptor as definitely assigned
     * to in this context.  */
    public void initializeField(VariableDescriptor varDesc) {
	((CFlowControlContext)delegee).initializeField(varDesc);
    }

    /**
     * Indicates whether the field in the given position is
     * definitely assigned to in this context.  */
    public boolean isFieldDefinitelyAssigned(int pos) {
	return ((CFlowControlContext)delegee).isFieldDefinitelyAssigned(pos);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (TYPE DEFINITION)
    // ----------------------------------------------------------------------

    /**
     * Adds to this context a class declared via a type declaration
     * statement.
     * @param	clazz		the clazz to add
     * @exception UnpositionedError	if duplicate class exists in this
     * lexical context */
    public void addLocalClass(CClass clazz) throws UnpositionedError {
	((CFlowControlContext)delegee).addLocalClass(clazz);
    }
 
    // ----------------------------------------------------------------------
    // ACCESSORS (NULLITY)
    // ----------------------------------------------------------------------

    protected /*@non_null*/ CContextNullity getContextNullity() {
       throw new RuntimeException("JmlFlowControlContext not allowed to access contextNullity");
    }
  
    /**
     * Indicates whether expr (or member) is conditionally NonNull is this context.
     */
    public /*@pure*/ boolean isFANonNull(/*@ non_null */ Object expr) {
          return ((CFlowControlContext)delegee).isFANonNull(expr);
    }
 
    /**
     * returns the JPhyla that are known to be non-null in this context.
     */
     public /*@pure*/ Object[] getFANonNulls() {
       return ((CFlowControlContext)delegee).getFANonNulls();
     }
     public /*@pure*/ Object[] getFANulls() {
       return ((CFlowControlContext)delegee).getFANulls();
     }

    /**
     * Mark expr (or member) as NonNull in this context
     */
    public void addFANonNull(Object expr) {
       ((CFlowControlContext)delegee).addFANonNull(expr);
    }
    public void addFANull(Object expr) {
       ((CFlowControlContext)delegee).addFANull(expr);
    }
    public void removeFANonNull(Object expr) {
       ((CFlowControlContext)delegee).removeFANonNull(expr);
    }
    public void removeAllFANullity() {
       ((CFlowControlContext)delegee).removeAllFANullity();
    }

    /**
     * adds exprs (or members) as NonNull in this context
     */
    public void addFANonNulls(Object[] exprs) {
	    if (delegee!=null)
       ((CFlowControlContext)delegee).addFANonNulls(exprs);
    }
    public void addFANulls(Object[] exprs) {
	    if (delegee!=null)
       ((CFlowControlContext)delegee).addFANulls(exprs);
    }

    /**
     * Merge the list of guarded nulls in this context with that of the given context.
     * This is done by taking a union of the two sets. 
     */
    public void mergeNullityInfo(CContextType other) {
       ((CFlowControlContext)delegee).mergeNullityInfo(other);
    }

    public void adoptNullityInfo(CContextType other) {
       ((CFlowControlContext)delegee).adoptNullityInfo(other);
    }

    public void dumpNonNulls(String msg) {
       ((CFlowControlContext)delegee).dumpNonNulls("(delegee is "+delegee.getClass()+")"+msg);
    }


    // ----------------------------------------------------------------------
    // ACCESSORS (LOOKUP)
    // ----------------------------------------------------------------------

    /**
     * Searches for a class with the given simple name according the
     * procedure in JLS2 6.5.5.  This method checks the first bullet
     * point of that section: "If the simple type name occurs within
     * the scope of a visible local class declaration with that name,
     * then the simple type name denotes that local class type."  If
     * no match is found, then this method calls to the surrounding
     * context to check the remaining bullet points.
     * 
     * @param	name	the class name, without qualifiers
     * @return	the class if found, null otherwise
     * @exception UnpositionedError if search fails */
    public CClass lookupClass(String name) throws UnpositionedError {
	return ((CFlowControlContext)delegee).lookupClass(name);
    }

    /**
     * Returns the variable referred to by the given name in this
     * context, recursing to surrounding contexts as appropriate.  If
     * no variable of the given name is found then <code>null</code>
     * is returned.
     *
     * @param	ident		the name of the variable */
    public JLocalVariable lookupLocalVariable(String ident) {
	JLocalVariable var 
	    = ((CFlowControlContext)delegee).lookupLocalVariable(ident);
	if( var != null ) {
	    long modifiers = var.modifiers();
	    if( hasFlag(modifiers, ACC_GHOST) && !JmlContext.inSpecScope()) {
		// ghost variables are not in scope unless in an 
		// annotation such as a set, assert, or assume statement. 
		return null;
	    }
	}
	return var;
    }

    /**
     * Indicates whether this context is enclosed in a loop and the
     * given variable is declared outside the inner-most loop
     * context. */
    public boolean declaredOutsideOfLoop(JLocalVariable var) {
	return ((CFlowControlContext)delegee).declares(var);
    }

    /**
     * Returns true if the given local variable is declared exactly in
     * this context, i.e., it is not declared in an outer context. */
    public boolean declares(JLocalVariable var) {
	return ((CFlowControlContext)delegee).declares(var);
    }

    // ----------------------------------------------------------------------
    // THROWABLES
    // ----------------------------------------------------------------------

    /**
     * @param	throwable	the type of the new throwable
     */
    public void addThrowable(CThrowableInfo throwable) {
	((CFlowControlContext)delegee).addThrowable(throwable);
    }

    /**
     * Default estimate of the number of local variable slots to
     * reserve.  */
    private static final int DEFAULT_VAR_ESTIMATE = 0;
}
