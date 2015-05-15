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
 * $Id: JmlExpressionContext.java,v 1.18 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContext;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.MJMathMode;
import org.multijava.util.compiler.UnpositionedError;

/**
 * A class for representing the context in which JML expressions
 * are typechecked. This is a subclass of the <tt>CExpressionContextType</tt>
 * class to encode the JML expression-specific contextual information.
 * For example, the JML <tt>\result</tt> expression is allowed only
 * in the normal postcondition. To typecheck the expressions such as 
 * <tt>\result</tt>, we pass to them the fact whether they are being 
 * typechecked in the normal postcondition or not as contexutal 
 * information.
 *
 * In JML, there are seven context(state)-sensitive expression
 * constructs: <tt>\fresh</tt>, <tt>\not_modified</tt>, <tt>\old</tt>,
 * <tt>\result</tt>, <tt>\duration</tt>, <tt>\working_space</tt>, and
 * <tt>\space</tt>. The typechecking rules for these constructs are
 * defined as follows. In the table, the entry with O means that a
 * particular construct is allowed in that particular context, and the
 * X marks prohibition.
 *
 * <pre>
 *  --------------------------------------------------------
 *                        \not_                   
 *                \fresh  modified  \old  \result    others
 *  -------------------------------------------------------
 *   pre           X      X          X      X        O    
 *   post (N)      O      O          O      O        O
 *   post (E)      O      O          O      X        O
 *   internal      O      O          O      X        O
 *   old           X      X          X      X        O
 *   intra         X      X          X      X        O
 *   inter         O      O          O      X        O
 *   working_space O      O          O      O        O
 *   duration      O      O          O      O        O
 *  ------------------------------------------------------
 * </pre>
 *
 * where the <em>precondition</em> is over a single, visible, definite
 * (determined) state (i.e., the pre-state); the normal or exceptional 
 * <em>postcondition</em> is over a pair of visible, definite states
 * (i.e., the pre/post-states); the <em>internal condition</em> is over
 * a pair of a pre-state and an invisible (internal, intermediate),
 * definite state (e.g., <tt>assert</tt> clause); 
 * the <em>old</em> condition is for the <tt>\old</tt> expression and should 
 * denote the pre-state, but we have separated them here for the future
 * extention;
 * the <em>intracondition</em> is over a single, visible, indefinite
 * (undetermined) state (i.e., some pre or post-state); 
 * the <em>intercondition</em> is over a pair of a pair of visible, 
 * undetermined states (i.e., some pre/post-states).
 * Both the intra- and intercondition are for class-level specifications
 * such as invariants (intracondition) and history constrainsts 
 * (intercondition).
 * The <em>working_space</em> is for the clause of the same name,
 * as is the <em>duration</em> context; both of these are assertions
 * over pairs of states, a pre-state and a post-state
 */
public class JmlExpressionContext extends JmlContext
    implements CExpressionContextType {

    // ----------------------------------------------------------------------
    // FACTORY METHODS
    // ----------------------------------------------------------------------

    /** Create and return a precondition context.
     *
     * @param parent the parent context
     * @return a new precondition context */
    public static /*@non_null@*/  JmlExpressionContext 
	createPrecondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_PRECONDITION );
    }

    /** Create and return a normal postcondition context.
     *
     * @param parent the parent context
     * @return a new postcondition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createPostcondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_POSTCONDITION );
    }

    /** Create and return an exceptional postcondition context.
     *
     * @param parent the parent context
     * @return a new exceptional postcondition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createExceptionalPostcondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, 
					  CTX_EXCEPTIONAL_POSTCONDITION );
    }

    /** Create and return a working_space context.
     *
     * @param parent the parent context
     * @return a new working_space context */
    public static /*@non_null@*/ JmlExpressionContext 
	createWorkingSpace( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_WORKING_SPACE );
    }

    /** Create and return a duration context.
     *
     * @param parent the parent context
     * @return a new duration context */
    public static /*@non_null@*/ JmlExpressionContext 
	createDuration( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_DURATION );
    }

    /** Create and return an internal condition context. An internal
     * condition context is for typechecking predicates over 
     * client-invisible, intermediate states such as <tt>assert</tt> 
     * clause.
     *
     * @param parent the parent context
     * @return a new internal condition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createInternalCondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_INTERNAL_CONDITION );
    }

    /** Create and return an old expression context. An old expression
     * context is for typechecking <tt>old</tt> expressions.
     *
     * @param parent the parent context
     * @return a new old expression condition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createOldExpression( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_OLD_EXPRESSION );
    }

    /** Create and return an intracondition context. An intracondition
     * context is for typechecking class-level specifications such as
     * <tt>invariant</tt> clause that concern with a single state.
     *
     * @param parent the parent context
     * @return a new intracondition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createIntracondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_INTRACONDITION );
    }

    /** Create and return an intercondition context. An intercondition
     * context is for typechecking class-level specifications such as
     * <tt>constraint</tt> clause that concern with a pair of states.
     *
     * @param parent the parent context
     * @return a new intercondition context */
    public static /*@non_null@*/ JmlExpressionContext 
	createIntercondition( /*@non_null@*/ CFlowControlContextType parent ) {
	return new JmlExpressionContext( parent, CTX_INTERCONDITION );
    }

    /** Return a new <tt>JmlExpressionContext</tt> of the same kind
     * as the given argument <tt>ctx</tt>.
     *
     * @param parent the parent context
     * @return a new context */
    public static /*@non_null@*/ JmlExpressionContext 
	createSameKind( /*@non_null@*/ CFlowControlContextType parent,  /*@non_null@*/ JmlExpressionContext ctx ) {
	return new JmlExpressionContext( parent, ctx.kind );
    }

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    private JmlExpressionContext(/*@non_null@*/ CFlowControlContextType parent, int kind) {
	super(parent);
	this.kind = kind;
	delegee = new CExpressionContext(parent);
        constructorHelper(parent);
    }

    private JmlExpressionContext(/*@non_null*/ JmlExpressionContext parent) {
	super(parent);
	this.kind = parent.kind;
	delegee = new CExpressionContext(parent);
        constructorHelper(parent);
    }

    /*@helper*/
    private void constructorHelper(/*@non_null*/ CContextType parent) {
	if(parent instanceof JmlContext){
		CMethod method = ((JmlContext)parent).getCMethod();
		CClass hostClass = ((JmlContext)parent).getHostClass();
		if(method != null && method instanceof org.jmlspecs.checker.JmlSourceMethod && ((JmlSourceMethod)method).getAST() instanceof JmlMethodDeclaration){
			JmlMethodDeclaration ast = ((JmlMethodDeclaration)((JmlSourceMethod)method).getAST());
			if(ast != null && !inSpecScope()){
				//System.out.println("(M) take code: " + ast.jmlAccess().codeArithmeticMode());
				arithmeticMode = ast.jmlAccess().codeArithmeticMode();
			}else if(ast != null && inSpecScope()){
				//System.out.println("(M) take spec: " + ast.jmlAccess().specArithmeticMode());
				arithmeticMode = ast.jmlAccess().specArithmeticMode();
			}else{
				//System.out.println("(M) take super: " + super.arithmeticMode());
				arithmeticMode = super.arithmeticMode();
			}
		}else if(hostClass != null && hostClass instanceof org.jmlspecs.checker.JmlSourceClass && ((JmlSourceClass)hostClass).getAST() instanceof JmlTypeDeclaration){
			JmlTypeDeclaration ast = ((JmlTypeDeclaration)((JmlSourceClass)hostClass).getAST());
			if(ast != null && !inSpecScope()){
				//System.out.println("(C) take code: " + ast.jmlAccess().codeArithmeticMode());
				arithmeticMode = ast.jmlAccess().codeArithmeticMode();				
			}else if(ast != null && inSpecScope()){
				//System.out.println("(C) take spec: " + ast.jmlAccess().specArithmeticMode());
				arithmeticMode = ast.jmlAccess().specArithmeticMode();
			}else{
				//System.out.println("(C) take super: " + super.arithmeticMode());
				arithmeticMode = super.arithmeticMode();
			}
		}else{
			//System.out.println("(!M & !C) take super: " + super.arithmeticMode());
			arithmeticMode = super.arithmeticMode();
		}
	}else{
		//System.out.println("(!JmlContext) take super: " + super.arithmeticMode());
		arithmeticMode = super.arithmeticMode();
	}
	
//	if(inSpecScope()){
//		arithmeticMode = AMID_BIGINT_MATH;
//	}else{
//		arithmeticMode = super.arithmeticMode();
//	}

    }
    // ----------------------------------------------------------------------
    // ACCESSORS (NEW CONTEXT)
    // ----------------------------------------------------------------------

	/**
	 * Create a copy of this context to handle divergent paths, e.g., in 
	 * conditional expressions
	 */
	public /*@non_null*/ CExpressionContextType createExpressionContext_() {
		return new JmlExpressionContext(this);
	}


    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * searches for a field with the given identifier
     * @return a field from an ident in current context
     * @exception	UnpositionedError	this error will be positioned soon
     */
    public /*@ nullable */ CFieldAccessor lookupField(/*@non_null@*/ String ident) throws UnpositionedError {
	return lookupField(ident, this);
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
    public /*@ nullable */ CFieldAccessor lookupOuterField(/*@non_null@*/ String ident)
	throws UnpositionedError {
	return lookupOuterField( ident, this );
    }

    /**
     * Set this context as an increment or decrement expression, so
     * we can generate appropriate getters and setters if necessary
     * (and also generate proper code in the future).
     * @param	incDec
     */
    public void setIncDec(boolean incDec) {
	((CExpressionContext)delegee).setIncDec(incDec);
    }

    /**
     * @return	true if this context is part of an increment or decrement
     * 		expression
     */
    public boolean isIncDec() {
	return ((CExpressionContext)delegee).isIncDec();
    }

    /**
     * Set this context as a left side in an assignment, so access to vars
     * may be uninitialized
     * @param	leftSide		set the side of current code flow
     */
    public void setLeftSide(boolean leftSide) {
	((CExpressionContext)delegee).setLeftSide(leftSide);
    }

    /**
     * @return	true if this context is on a left side of an assignement
     */
    public boolean isLeftSide() {
	return ((CExpressionContext)delegee).isLeftSide();
    }

    /**
     * set this context as a discarded value so result is ignored
     * @param	discardValue	is the value of this expression in 
     *				this context discarded?
     */
    public void setDiscardValue(boolean discardValue) {
	((CExpressionContext)delegee).setDiscardValue(discardValue);
    }

    /**
     * @return	true if the result value of this expression is discarded
     */
    public boolean discardValue() {
	return ((CExpressionContext)delegee).discardValue();
    }

    // ----------------------------------------------------------------------
    // JML-SPECIFIC ACCESSORS
    // ----------------------------------------------------------------------

    /** Return true if <tt>\fresh</tt> is allowed in this context */
    public boolean freshOk() {
	switch (kind) {
	case CTX_POSTCONDITION:
	case CTX_EXCEPTIONAL_POSTCONDITION:
	case CTX_INTERNAL_CONDITION:
	case CTX_INTERCONDITION:
	case CTX_WORKING_SPACE:
        case CTX_DURATION:
	    return true;
	default:
	    return false;
	}
    }

    /** Return true if <tt>\not_modified</tt> is allowed in this context */
    public boolean notModifiedOk() {
	switch (kind) {
	case CTX_POSTCONDITION:
	case CTX_EXCEPTIONAL_POSTCONDITION:
	case CTX_INTERNAL_CONDITION:
	case CTX_INTERCONDITION:
	case CTX_WORKING_SPACE:
        case CTX_DURATION:
	    return true;
	default:
	    return false;
	}
    }

    /** Return true if <tt>\old</tt> expression is allowed in this context */
    public boolean oldOk() {
	switch (kind) {
	case CTX_POSTCONDITION:
	case CTX_EXCEPTIONAL_POSTCONDITION:
	case CTX_INTERNAL_CONDITION:
	case CTX_INTERCONDITION:
	case CTX_WORKING_SPACE:
        case CTX_DURATION:
	    return true;
	default:
	    return false;
	}
    }

    /** Return true if <tt>\result</tt> is allowed in this context */
    public boolean resultOk() {
	switch (kind) {
	case CTX_POSTCONDITION:
	case CTX_WORKING_SPACE:
        case CTX_DURATION:
	    return true;
	default:
	    return false;
	}
    }

    // ----------------------------------------------------------------------
    // Get/set methods
    // ----------------------------------------------------------------------
    
    public /*@non_null@*/ MJMathMode arithmeticMode() {
	return arithmeticMode;
    }

    public void setArithmeticMode(byte mode) {
	arithmeticMode = JMLMathMode.newJMLMathMode(mode);
    }

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

    //@ invariant (* kind is one of CTX_xxx *);
    private int kind;

    private static final int CTX_PRECONDITION              = 0;
    private static final int CTX_POSTCONDITION             = 1;
    private static final int CTX_EXCEPTIONAL_POSTCONDITION = 2;
    private static final int CTX_INTERNAL_CONDITION        = 3;
    private static final int CTX_OLD_EXPRESSION            = 4;
    private static final int CTX_INTRACONDITION            = 5;
    private static final int CTX_INTERCONDITION            = 6;
    private static final int CTX_WORKING_SPACE             = 7;
    private static final int CTX_DURATION                  = 8;
    
    protected	/*@non_null@*/ MJMathMode		arithmeticMode;
}
