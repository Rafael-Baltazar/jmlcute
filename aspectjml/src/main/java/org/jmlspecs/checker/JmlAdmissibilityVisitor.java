/*
 * Copyright (C) 2005-2006 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
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
 */

package org.jmlspecs.checker;

import java.util.Stack;

import org.jmlspecs.ajmlrac.qexpr.AbstractExpressionVisitor;
import org.multijava.mjc.CArrayType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CType;
import org.multijava.mjc.CUniverse;
import org.multijava.mjc.CUniversePeer;
import org.multijava.mjc.CUniverseReadonly;
import org.multijava.mjc.CUniverseRep;
import org.multijava.mjc.JArrayAccessExpression;
import org.multijava.mjc.JArrayDimsAndInits;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JConditionalExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JUnaryPromote;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.MessageDescription;
import org.multijava.util.compiler.PositionedError;

/**
 * A visitor class to check admissibility of JML invariants and represents
 * clauses. Static invariants and static represents clauses, as well as
 * static fields and methods calls appearing in invariants
 * and represents clauses are not yet supported.
 * 
 * For more datails about admissibility see
 * "Modular Invariants for Layered Object Structures" by
 * P. Mueller, A. Poetzsch-Heffter and G. Leavens, 2004.
 * 
 * FIXME: Known Issues:
 * 
 * 1. New Array Creation with Initializer:
 *    new Object{peerfield}[0] is admissible but rejected.
 *    Hard to fix (IMHO)
 * 
 * 2. Hidden this:
 *    (field < 0 ? this : this).field == 0 is admissible but rejected.
 *    Quite easy to fix (IMHO)
 * 
 * @author rzakhejm
 * @version 0.01
 */
public abstract class JmlAdmissibilityVisitor extends AbstractExpressionVisitor {
	
	// ----------------------------------------------------------------------
	// CONSTANTS SECTION
	// ----------------------------------------------------------------------

	/** Command line option to enable classical admissibility checks
	 */
	public static final String ADMISSIBILITY_CLASSICAL = "classical";
 
	/** Command line option to disable admissibility checks
	 */
	public static final String ADMISSIBILITY_NONE = "none";

	/** Command line option to enable ownership admissibility checks
	 */
	public static final String ADMISSIBILITY_OWNERSHIP = "ownership";	
	
	// ----------------------------------------------------------------------
	// STATICS SECTION
	// ----------------------------------------------------------------------

	/**
	 * Admissibility checks an invariant. The invariant should already be typechecked.
	 * @param expr The invariant to check
	 * @param ectx its context
	 * @return whether the invariant is admissible
	 */
	public static boolean checkInvariant(/*@non_null*/ JmlInvariant expr, /*@non_null*/ JmlExpressionContext ectx) {
		return checkAdmissibility(expr.predicate(), ectx, null);
	}

	/**
	 * Admissibility checks a represents clause. Both, functional and relational clauses are supported.
	 * The represents clause should already be typechecked. 
	 * @param decl The represents clause to check
	 * @param ectx its context
	 * @return whether the represents clause is admissible
	 */
	public static boolean checkRepresentsClause(/*@non_null*/ JmlRepresentsDecl decl, /*@non_null*/ JmlExpressionContext ectx) {
		JExpression expr;
		if (decl.usesAbstractionFunction())
			expr = decl.specExpression();
		else
			expr = decl.predicate();
		return checkAdmissibility(expr, ectx, decl.getField());
	}
	
	/**
	 * Are the admissibility checks enabled ?
	 * @return true if some admissibility check is enabled
	 */
	public static boolean isAdmissibilityCheckEnabled() {
		return getAdmissibility() != JmlAdmissibilityVisitor.ADMISSIBILITY_NONE;
	}
	
	/**
	 * Is the ownership admissibility check enabled ?
	 * @return true if the ownership admissibility check is enabled
	 */
	public static boolean isAdmissibilityOwnershipEnabled() {
		return getAdmissibility() == JmlAdmissibilityVisitor.ADMISSIBILITY_OWNERSHIP;
	}
	
	/**
	 * Admissibility checks a JExpression.
	 * @param expr the predicate to check
	 * @param ectx its context
	 * @param modelField the modelfield to check in case of a represents clause or null
	 * in case of an invariant.
	 * @return whether errors or warnings occured during checking
	 */
	protected static boolean checkAdmissibility(JExpression expr, JmlExpressionContext ectx, CFieldAccessor modelField) {
		JmlAdmissibilityVisitor visitor = getVisitor();
		if (visitor == null)
			return true;
		visitor.ectx = ectx;
		visitor.modelField = modelField;
		try {
			visitor.visit(expr);
		} catch (NotAdmissibleException e) {
		}
		return !visitor.hasErrorsOrWarnings;
	}
	
	/**
	 * If expr is of type JParenthesedExpression, this method returns
	 * the first child of expr which is not a JPatenthesedExpression.
	 * @param expr the expression to remove its parentheses.
	 * @return the first child of expr not a parentheses.
	 */
	protected static JExpression removeParentheses(JExpression expr) {
		while (expr instanceof JParenthesedExpression)
			expr = ((JParenthesedExpression) expr).expr();
		return expr;
	}
	
	/**
	 * Whether the expr, after removing casts (JCastExpression, JUnaryPromote)
	 * is of type JThisExpression.
	 * @param expr to check for a this in casts
	 * @return whether it is a this after casts.
	 */
	protected static boolean isThisAfterCasts(JExpression expr) {
		while (expr instanceof JCastExpression || expr instanceof JUnaryPromote) {
			if (expr instanceof JCastExpression)
				expr = removeParentheses(((JCastExpression) expr).expr());
			else
				expr = removeParentheses(((JUnaryPromote) expr).expr());
		}
		return expr instanceof JThisExpression;
	}
	
	/**
	 * This method takes the command line admissibility string and returns the appropriate canonical
	 * admissibility option string.
	 * @return the canonical admissibility option string corresponding to the command line option,
	 * i.e. ownership, classical or none.
	 * @see #ADMISSIBILITY_CLASSICAL
	 * @see #ADMISSIBILITY_OWNERSHIP
	 * @see #ADMISSIBILITY_NONE
	 */
	private static String getAdmissibility() {
		String admissibility = "";// Main.jmlOptions.admissibility();
		if (admissibility.equals(ADMISSIBILITY_CLASSICAL)) {
			return ADMISSIBILITY_CLASSICAL;
		} else if (admissibility.equals(ADMISSIBILITY_OWNERSHIP)) {
			return ADMISSIBILITY_OWNERSHIP;
		} else {
			return ADMISSIBILITY_NONE;
		}
	}
	
	/**
	 * Returns a new instance of the appropriate subclass of JmlAdmissibilityVisitor or null 
	 * according to the chosen command line option "ownership", "classical" or "none."
	 * @return a new instance of a subclass of JmlAdmissibilityVisitor for the options
	 * "ownership" and "classical", or <code>null</code> for "none".
 	 */
	private static JmlAdmissibilityVisitor getVisitor() {
		String admissibility = getAdmissibility();
		if (admissibility.equals(ADMISSIBILITY_CLASSICAL))
			return new JmlClassicalAdmissibilityVisitor();
		else if (admissibility.equals(ADMISSIBILITY_OWNERSHIP))
			return new JmlOwnershipAdmissibilityVisitor();	
		else
			return null;
	}
	
	// ----------------------------------------------------------------------
	// INSTANCE SECTION
	// ----------------------------------------------------------------------
	
	/**
	 * The context of the expression to check
	 */
	protected JmlExpressionContext ectx = null;
	
	/**
	 * Whether warnings or errors occured during the admissibility check.
	 * Errors and warnings are not distinguished since in both cases admissibility
	 * is not (yet) assured. An error occures when an expression is not admissible,
	 * a warning when certain language constructs are not (yet) supported.
	 */
	protected boolean hasErrorsOrWarnings = false;
	
	/**
	 * In the case of a represents clause, this field saves a reference to the
	 * model field, in order to enable it to appear in the represents expression
	 * and to ignore subclass separation for this field.
	 */
	protected CFieldAccessor modelField = null;

	/**
	 * Emits a warning. Currently all admissibility errors are emitted as
	 * warnings.
	 * @param expr the expression the warning occured in.
	 * @param desc the warning message.
	 */
	protected void warn(JExpression expr, MessageDescription desc) throws NotAdmissibleException {
		try {
			expr.warn(ectx.getParentContext(), desc, expr);
			hasErrorsOrWarnings = true;
			if (desc.getLevel() == 0)
				throw new NotAdmissibleException();
		} catch (PositionedError e) {
			ectx.reportTrouble(e);
		}		
	}
	
	/**
	 * This method calls the {@link JExpression#accept(MjcVisitor)} method of expr. It enables subclasses overridding
	 * this method to introduce custom initialization and termination control.
	 * @param expr The expr to be visited by this.
	 */
	protected void visit(JExpression expr) {
		expr.accept(this);
	}
	
	/**
	 * An Exception which is thrown when some was found not to be admissible. This
	 * Exception is a subclass of {@link RuntimeException}, since otherwise the
	 * signature of {@link JExpression#accept(MjcVisitor)} must be changed.
	 * Currently this exception is caught by checkAdmissibility.
	 */
	protected class NotAdmissibleException extends RuntimeException {
		
	}
}

class JmlClassicalAdmissibilityVisitor extends JmlAdmissibilityVisitor {
	
	// ----------------------------------------------------------------------
	// VISITORS
	// ----------------------------------------------------------------------

	/** Visits the given array access expression,
	 * <code>self</code>. By default, this method visits both prefix
	 * and accessor of <code>self</code>. An array access is never
	 * classically admissible. */
	public void visitArrayAccessExpression(
	/*@ non_null @*/JArrayAccessExpression self) {
		warn(self, JmlMessages.NOT_ADMISSIBLE);
		self.prefix().accept(this);
		self.accessor().accept(this);
	}

	/** Visits the given class field expression, <code>self</code>.  By
	 * default, this method visits the prefix of <code>self</code> if
	 * it is not null. */
	public void visitFieldExpression(
	/*@ non_null@*/JClassFieldExpression self) {
		JExpression prefix = removeParentheses(self.prefix());
		CFieldAccessor field = self.getField();
		if (prefix != null) {
			if (!field.isFinal()) { // then Rule 1 else Rule 2
				if (field.isStatic())
					warn(self, JmlMessages.ADMISSIBILITY_STATICS_NOT_SUPPORTED);
				else {
					if (!isThisAfterCasts(prefix)) { // Rule 1
						warn(self, JmlMessages.NOT_ADMISSIBLE);						
					} else if (!(field.equals(modelField) || field.owner().equals(ectx.getHostClass()))) { // Rule 1
						warn(self, JmlMessages.NOT_ADMISSIBLE);
					}
				}
			}
			prefix.accept(this);
		}
	}

	/** Visits the given method expression, <code>self</code>. By
	 * default, this method visits both prefix and arguments of
	 * <code>self</code>. Method calls are not supported yet, but the 
	 * receiver object and the method parameters are checked. */
	public void visitMethodCallExpression(
	/*@ non_null @*/JMethodCallExpression self) {
		warn(self, JmlMessages.ADMISSIBILITY_METHOD_CALL_NOT_SUPPORTED);
		if (self.prefix() != null) {
			self.prefix().accept(this);
		}
		visitExpressions(self.args());
	}

	/** Visits the given new object expression,
	 * <code>self</code>. By default, this method visits both the
	 * this expression and parameters of <code>self</code>. Object creation
	 * is not supported yet, but the receiver object and the parameters are checked.*/
	public void visitNewObjectExpression(
	/*@ non_null @*/JNewObjectExpression self) {
		warn(self, JmlMessages.ADMISSIBILITY_OBJECT_CREATION_NOT_SUPPORTED);
		if (self.thisExpr() != null) {
			self.thisExpr().accept(this);
		}
		visitExpressions(self.params());
	}
	
	// ----------------------------------------------------------------------
	// HELPERS
	// ----------------------------------------------------------------------

}

class JmlOwnershipAdmissibilityVisitor extends JmlAdmissibilityVisitor {
	
	/**
	 * Indicates whether the pivot field g0 must be a rep field, i.e. whether
	 * rule 3 must be applied.
	 */
	private boolean needsRep = false;

	/**
	 * Indicates whether the declared array base-type universe modifier
	 * must be checked when accessing the array.
	 */
	private boolean needsArrayBaseNotReadOnly = false;

	/**
	 * Was something casted to rep ? Needed for arrays casted to rep to remember
	 * that it was casted.
	 * 
	 * @see #visitArrayAccessExpression(JArrayAccessExpression)
	 */
	private boolean isCastedToRep = false;

	/**
	 * In order to get meaningful error messages, the JExpression where needsRep
	 * was set is stored.
	 */
	private JExpression potentiallyNotAdmissible = null;
	
	/**
	 * The state of this JmlOwnershipAdmissibilityVisitor is often saved at the beginning of 
	 * a visit-method, and restored at its end. To avoid tedious introduction of local variables
	 * and so on, stateStack can be used to save, restore and clear the current state.
	 * 
	 * @see #pushState()
	 * @see #popState()
	 * @see #clearCurrentState()
	 * @see JmlOwnershipAdmissibilityVisitor.State
	 */
	private final Stack stateStack = new Stack();
	
	/**
	 * A data structure to store the current state of this visitor.
	 */
	static private class State {
		
		/**
		 * A copy of the state of constructor's visitor parameter
		 */
		boolean needsRep, needsArrayBaseNotReadonly, isCastedToRep;
		JExpression potentiallyNotAdmissible;
		/**
		 * Create a new State object and copy visitor's state into the newly created object.
		 * @param visitor The visitor to generate a State object containing visitors state.
		 */
		public State(JmlOwnershipAdmissibilityVisitor visitor) {
			this.isCastedToRep = visitor.isCastedToRep;
			this.needsRep = visitor.needsRep;
			this.needsArrayBaseNotReadonly = visitor.needsArrayBaseNotReadOnly;
			this.potentiallyNotAdmissible = visitor.potentiallyNotAdmissible;
		}
	}
	
	/**
	 * Stores a copy of the current state and pushes this copy onto the top
	 * if stateStack. The state of "this" is left unchanged.
	 */
	private void pushState() {
		stateStack.push(new State(this));
	}
	
	/**
	 * Restores the last pushed state. The st
	 */
	private void popState() {
		State state = (State) stateStack.pop();
		this.isCastedToRep = state.isCastedToRep;
		this.needsRep = state.needsRep;
		this.needsArrayBaseNotReadOnly = state.needsArrayBaseNotReadonly;
		this.potentiallyNotAdmissible = state.potentiallyNotAdmissible;		
	}
	
	/**
	 * Clears the current state of this visitor, i.e. sets all fields to their initial value.
	 * {@link #stateStack} is not affected.
	 */
	private void clearCurrentState() {
		isCastedToRep = false;
		needsRep = false;
		potentiallyNotAdmissible = null;
		needsArrayBaseNotReadOnly = false;
	}

	/* (non-Javadoc)
	 * @see org.jmlspecs.checker.JmlAdmissibilityVisitor#visit(org.multijava.mjc.JExpression)
	 */
	protected void visit(JExpression expr) {
		super.visit(expr);
		assertTrue(stateStack.isEmpty(), "Internal Error: StateStack not empty after admissibility check !");
	}

	
	// ----------------------------------------------------------------------
	// VISITORS
	// ----------------------------------------------------------------------

	/** Visits the given array access expression,
	 * <code>self</code>. By default, this method visits both prefix
	 * and accessor of <code>self</code>.
	 * The logic is as follows:
	 * needsRep && isCastedToRep && isArrayBaseElement: impossible
	 * needsRep && isCastedToRep && !isArrayBaseElement: impossible
	 * needsRep && !isCastedToRep && isArrayBaseElement: set needsArrayBaseNotReadOnly
	 * needsRep && !isCastedToRep && !isArrayBaseElement: no action
	 * !needsRep && isCastedToRep && isArrayBaseElement: clear isCastedToRep, set needsRep
	 * !needsRep && isCastedToRep && !isArrayBaseElement: no action
	 * !needsRep && !isCastedToRep && isArrayBaseElement: set needsRep
	 * !needsRep && !isCastedToRep && !isArrayBaseElement: set needsRep
	 * 
	 */
	public void visitArrayAccessExpression(
	/*@ non_null @*/JArrayAccessExpression self) {
		pushState();
		final boolean isArrayBaseElement = self.getType().isClassType() && !self.getType().isArrayType();
		if (isArrayBaseElement) {
			isCastedToRep = false;
		}
		if (!needsRep) { // Rule 3
			if (!isCastedToRep) {     
				potentiallyNotAdmissible = self;
				needsRep = true;
			}
		} else if (isArrayBaseElement) { // universe modifier must be check later
				needsArrayBaseNotReadOnly = true;
		}
		self.prefix().accept(this);
		clearCurrentState();
		self.accessor().accept(this);
		popState();
	}

	/** Visits the given class field expression, <code>self</code>.  By
	 * default, this method visits the prefix of <code>self</code> if
	 * it is not null. */
	public void visitFieldExpression(
			/*@ non_null@*/JClassFieldExpression self) {
		pushState();
		JExpression prefix = removeParentheses(self.prefix());
		CFieldAccessor field = self.getField();
		if (needsArrayBaseNotReadOnly) {
			CType type = field.getType();
			if (type instanceof CArrayType) {
				CType baseType = ((CArrayType) type).getDeclaredBaseType();
				if (baseType instanceof CClassType) {
					CUniverse univ = ((CClassType) baseType).getCUniverse();
					if (univ instanceof CUniverseReadonly)
						warn(potentiallyNotAdmissible, JmlMessages.NOT_ADMISSIBLE);
				}
			} else {
				// Array which was casted to Object - we don't know anything about the base type
				// (or we are in a new array initializer...)
				warn(potentiallyNotAdmissible, JmlMessages.NOT_ADMISSIBLE);
			}
			needsArrayBaseNotReadOnly = false;
		}
		if (prefix != null) {
			if (isThisAfterCasts(prefix)) {   // g0
				if (field.isStatic() && (needsRep || !field.isFinal()))
					// final static is OK if !needsRep, Rule 2
					warn(self, JmlMessages.ADMISSIBILITY_STATICS_NOT_SUPPORTED);
				else if (!field.equals(modelField) && !field.owner().equals(ectx.getHostClass())) {
					// even if needsRep == true, warning needed for subclass separation
					warn(self, JmlMessages.NOT_ADMISSIBLE);
				} else if (needsRep) { // g0 from N > 0
					CType type = field.getType();
					if (type instanceof CClassType) { // since needsRep is set, self was dereferenced
						CUniverse univ = ((CClassType) type).getCUniverse();
						if (!(univ instanceof CUniverseRep)) // Rule 3
							warn(potentiallyNotAdmissible, JmlMessages.NOT_ADMISSIBLE);
					} else {
						// can happen within a new array initializer
					}
					needsRep = false;
					potentiallyNotAdmissible = null;
				}
			} else if (prefix instanceof JSuperExpression) {
				if (needsRep || !field.isFinal())
					// no subclass separation
					warn(self, JmlMessages.NOT_ADMISSIBLE);				
			} else {
				if (field.isStatic() && (needsRep || !field.isFinal())) {
					warn(self, JmlMessages.ADMISSIBILITY_STATICS_NOT_SUPPORTED);
				} else {
					if (needsRep) { // g1 - gN-1 for N > 0
						CType type = field.getType();
						if (type instanceof CClassType) {
							CUniverse univ = ((CClassType) type).getCUniverse();
							if (univ instanceof CUniverseReadonly)
								warn(potentiallyNotAdmissible, JmlMessages.NOT_ADMISSIBLE);
						} else {
							// can happen within a new array initializer
						}
					} else { // gN with N > 0 
						if (!field.isFinal()) { // Rule 3, else Rule 2
							needsRep = true;
							potentiallyNotAdmissible = self;
						}
					}
				}
			}
			isCastedToRep = false;
			prefix.accept(this);
		}
		popState();
	}

	/** Visits the given method expression, <code>self</code>. By
	 * default, this method visits both prefix and arguments of
	 * <code>self</code>. Method calls are not supported yet, but the 
	 * receiver object and the method parameters are checked.*/
	public void visitMethodCallExpression(
	/*@ non_null @*/JMethodCallExpression self) {
		pushState();
		warn(self, JmlMessages.ADMISSIBILITY_METHOD_CALL_NOT_SUPPORTED);
		/* if (needsRep)
			 (* check return type - not done yet since method calls not yet supported *) */
		clearCurrentState();
		if (self.prefix() != null) {
			self.prefix().accept(this);
		}
		visitExpressions(self.args());
		popState();
	}
	
	/** Visits the given new object expression,
	 * <code>self</code>. By default, this method visits both the
	 * this expression and parameters of <code>self</code>. Object creation
	 * is not supported yet, but the receiver object and the parameters are checked. */
	public void visitNewObjectExpression(
	/*@ non_null @*/JNewObjectExpression self) {
		pushState();
		warn(self, JmlMessages.ADMISSIBILITY_OBJECT_CREATION_NOT_SUPPORTED);
		clearCurrentState();
		if (self.thisExpr() != null) {
			self.thisExpr().accept(this);
		}
		visitExpressions(self.params());
		popState();
	}
	
    /**
     * Visits the given conditional expression, <code>self</code>.  By
     * default, this method visits the condition, left and right
     * expressions of <code>self</code>.
     */
    public void visitConditionalExpression( 
        /*@ non_null @*/ JConditionalExpression self ) {
    	pushState();
		self.left().accept(this);
		self.right().accept(this);
		clearCurrentState();
		self.cond().accept(this);
		popState();
    }
    
    /** Visits the given array dimension and initializer,
	 * <code>self</code>. By default, this method visits both the
	 * dimension expression and initializer of <code>self</code>. */
	public void visitArrayDimsAndInit(
	/*@ non_null @*/JArrayDimsAndInits self) {
		pushState();
		if (self.init() != null) {
			self.init().accept(this);
		}
		clearCurrentState();
		visitExpressions(self.dims());
		popState();
	}
	
    /** Visits the given this expression, <code>self</code>. By
     * default, this method does nothing. */
    public void visitThisExpression( 
        /*@ non_null @*/ JThisExpression self ) {
    	if (needsRep)
    		warn(potentiallyNotAdmissible, JmlMessages.NOT_ADMISSIBLE);
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
    }

    /** Visits the given cast expression, <code>self</code>. By
	 * default, this method visits the expression of
	 * <code>self</code>. If the cast does not involve universe types,
	 * then there is no problem, otherwise ... */
	public void visitCastExpression(
	/*@ non_null @*/JCastExpression self) {
		pushState();
		final CType exprtype = self.expr().getType();
		final CType casttype = self.getType();
		if (exprtype instanceof CClassType && casttype instanceof CClassType) { // second check possibly not needed
			CClassType castclasstype = (CClassType) casttype;
			CClassType exprclasstype = (CClassType) exprtype;
			if (!castclasstype.getCUniverse().equals(exprclasstype.getCUniverse())) {
				// Universe cast
				CUniverse isCastedTo = castclasstype.getCUniverse();
				if (isCastedTo instanceof CUniverseRep) {
					// we can start from beginning
					needsRep = false;
					// potentiallyNotAdmissible not reset, since possibly needed by needsArrayBaseNotReadOnly
					isCastedToRep = true;
				} /* else if (isCastedTo instanceof CUniversePeer) {
					if (needsRep) {
						warn(self, JmlMessages.NOT_ADMISSIBLE);
					} else {
						// seems to be empty, i.e. do nothing
					}
				} */
			}
			if (needsArrayBaseNotReadOnly && castclasstype.isArrayType()) { // castclasstype, since exprclasstype could be Object
				CArrayType castarraytype = (CArrayType) casttype;
				// FIXME @ assert castarraytype.getDeclaredBaseType() instanceof CClassType; // since  needsArrayBaseNotReadOnly is set
				if (castarraytype.getDeclaredBaseType().isClassType()) {
					CUniverse baseuniv = ((CClassType) castarraytype.getDeclaredBaseType()).getCUniverse();
					if (baseuniv instanceof CUniversePeer) {
						needsArrayBaseNotReadOnly = false;
					}
				}
			}
		}
		self.expr().accept(this);
		popState();
	}
	
	// ----------------------------------------------------------------------
	// Question marks
	// ----------------------------------------------------------------------

//    /**
//     * Visits the given \reach expression, <code>self</code>.  By
//     * default, this method visits the store reference expression of
//     * <code>self</code>. PROBLEM !
//     */
//    public void visitJmlReachExpression( 
//        /*@ non_null @*/ JmlReachExpression self ) {
//        if (self.storeRefExpression() != null) {
//            self.storeRefExpression().accept(this);
//        }
//    }
//
//    /**
//     * Visits the given set comprehension expression,
//     * <code>self</code>.  By default, this method visits boeth
//     * predicate and superset predicate of <code>self</code>. DON'T KNOW.
//     */
//    public void visitJmlSetComprehension( 
//        /*@ non_null @*/ JmlSetComprehension self ) {
//
//        //@ assert self.predicate() != null;
//	self.predicate().accept(this);
//        //@ assert self.supersetPred() != null;
//	self.supersetPred().accept(this);
//    }
//
//    /**
//     * Visits the given \typeof expression, <code>self</code>.  By
//     * default, this method visits the spec expression of
//     * <code>self</code>. SEEMS TO BE OK.
//     */
//    public void visitJmlTypeOfExpression( 
//        /*@ non_null @*/ JmlTypeOfExpression self ) {
//	self.specExpression().accept(this);
//    }
//
//
//    /** Visits the given class expression, <code>self</code>. By
//     * default, this method does nothing. SEEMS TO BE OK. */
//    public void visitClassExpression( 
//        /*@ non_null @*/ JClassExpression self ) {
//    }
//
//    
//    /**
//     * Visits the given \type expression, <code>self</code>.
//     * By default, this method does nothing. SEEMS TO BE OK.
//     */
//    public void visitJmlTypeExpression( JmlTypeExpression self ) {
//    }
//    
//    /**
//     * Visits the given elem type expression,
//     * <code>self</code>. By default, this method visits the spec
//     * expression of <code>self</code>. SEEMS TO BE OK.
//     */
//    public void visitJmlElemTypeExpression( 
//        /*@ non_null @*/ JmlElemTypeExpression self ) {
//        //@ assert self.specExpression() != null;
//	self.specExpression().accept(this);
//    }
//    /** Visits the given unary promition expression,
//     * <code>self</code>. By default, this method visits the
//     * expression of of <code>self</code>. SEEMS TO BE OK.
//	   */
//    public void visitUnaryPromoteExpression( 
//        /*@ non_null @*/ JUnaryPromote self ) {
//	self.expr().accept(this);
//    }

}
