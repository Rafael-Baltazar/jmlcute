/*
 * Copyright (C) 2001, 2002 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: AbstractExpressionVisitor.java,v 1.13 2005/08/17 06:15:02 cruby Exp $
 */

package org.jmlspecs.ajmlrac.qexpr;

import org.jmlspecs.ajmlrac.RacAbstractVisitor;
import org.jmlspecs.checker.JmlDurationExpression;
import org.jmlspecs.checker.JmlElemTypeExpression;
import org.jmlspecs.checker.JmlFreshExpression;
import org.jmlspecs.checker.JmlInformalExpression;
import org.jmlspecs.checker.JmlInvariantForExpression;
import org.jmlspecs.checker.JmlIsInitializedExpression;
import org.jmlspecs.checker.JmlLabelExpression;
import org.jmlspecs.checker.JmlLockSetExpression;
import org.jmlspecs.checker.JmlMaxExpression;
import org.jmlspecs.checker.JmlNonNullElementsExpression;
import org.jmlspecs.checker.JmlOldExpression;
import org.jmlspecs.checker.JmlPreExpression;
import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlReachExpression;
import org.jmlspecs.checker.JmlRelationalExpression;
import org.jmlspecs.checker.JmlResultExpression;
import org.jmlspecs.checker.JmlSetComprehension;
import org.jmlspecs.checker.JmlSpaceExpression;
import org.jmlspecs.checker.JmlSpecExpression;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.jmlspecs.checker.JmlTypeExpression;
import org.jmlspecs.checker.JmlTypeOfExpression;
import org.jmlspecs.checker.JmlWorkingSpaceExpression;
import org.multijava.mjc.JAddExpression;
import org.multijava.mjc.JArrayAccessExpression;
import org.multijava.mjc.JArrayDimsAndInits;
import org.multijava.mjc.JArrayInitializer;
import org.multijava.mjc.JArrayLengthExpression;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JBinaryExpression;
import org.multijava.mjc.JBitwiseExpression;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JClassExpression;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JCompoundAssignmentExpression;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JConditionalExpression;
import org.multijava.mjc.JConditionalOrExpression;
import org.multijava.mjc.JDivideExpression;
import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExplicitConstructorInvocation;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JMinusExpression;
import org.multijava.mjc.JModuloExpression;
import org.multijava.mjc.JMultExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNewAnonymousClassExpression;
import org.multijava.mjc.JNewArrayExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JPostfixExpression;
import org.multijava.mjc.JPrefixExpression;
import org.multijava.mjc.JRelationalExpression;
import org.multijava.mjc.JShiftExpression;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JTypeNameExpression;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.mjc.JUnaryPromote;

/**
 * An abstract visitor class that visits all subexpressions of a given
 * expression recursively. This abstract visitor class facilitates
 * writing concrete expression visitor classes.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.13 $
 */
public abstract class AbstractExpressionVisitor extends RacAbstractVisitor {

    // ----------------------------------------------------------------------
    // VISITORS
    // ----------------------------------------------------------------------

    /**
     * Visits the given RAC predicate, <code>self</code>. By default,
     * this method visits the spec expression of <code>self</code>.
     */
    public void visitJmlPredicate(/*@ non_null @*/ JmlPredicate self) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given JML spec expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>.
     */
    public void visitJmlSpecExpression(
        /*@ non_null @*/ JmlSpecExpression self) {

        //@ assert self.expression() != null;
	self.expression().accept(this);
    }

    /**
     * Visits the given non-null element expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlNonNullElementsExpression(
	/*@ non_null @*/ JmlNonNullElementsExpression self) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \duration expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlDurationExpression(
        /*@ non_null @*/ JmlDurationExpression self){
        //@ assert self.expression() != null;
	self.expression().accept(this);
    }

    /**
     * Visits the given \working_space expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlWorkingSpaceExpression(
        /*@ non_null @*/ JmlWorkingSpaceExpression self){
        //@ assert self.expression() != null;
	self.expression().accept(this);
    }


    /**
     * Visits the given \space expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlSpaceExpression(
        /*@ non_null @*/ JmlSpaceExpression self){
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \max expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlMaxExpression( 
        /*@ non_null @*/ JmlMaxExpression self ) {
        //@ assert self.expression() != null;
	self.expression().accept(this);
    }

    /**
     * Visits the given elem type expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlElemTypeExpression( 
        /*@ non_null @*/ JmlElemTypeExpression self ) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given fresh expression, <code>self</code>. By
     * default, this method visits each spec expression contained in
     * the expression <code>self</code>.
     */
    public void visitJmlFreshExpression( 
        /*@ non_null @*/ JmlFreshExpression self ) {

        //@ assert self.specExpressionList() != null;
	JmlSpecExpression[] exprs = self.specExpressionList();
	for (int i = 0; i < exprs.length; i++) 
	    exprs[i].accept(this);
    }

    /**
     * Visits the given informal description expression, <code>self</code>. By
     * default, this method does no action at all.
     */
    public void visitJmlInformalExpression( JmlInformalExpression self ) {
    }

    /**
     * Visits the given \invariant_for expression,
     * <code>self</code>. By default, this method visits the spec
     * expression of <code>self</code>.
     */
    public void visitJmlInvariantForExpression(
        /*@ non_null @*/ JmlInvariantForExpression self){
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \is_initialized expression,
     * <code>self</code>. By default, this method does nothing.
     */
    public void visitJmlIsInitializedExpression( 
        /*@ non_null @*/ JmlIsInitializedExpression self) {
    }

    /**
     * Visits the given label expression, <code>self</code>. By
     * default, this method visits the spec expression of
     * <code>self</code>.
     */
    public void visitJmlLabelExpression( 
        /*@ non_null @*/ JmlLabelExpression self ) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \lockset expression, <code>self</code>. By
     * default, this method does nothing.
     */
    public void visitJmlLockSetExpression( JmlLockSetExpression self ) {
    }

    /**
     * Visits the given \pre expression, <code>self</code>.  By
     * default, this method visits the spec expression of
     * <code>self</code>.
     */
    public void visitJmlPreExpression( 
        /*@ non_null @*/ JmlPreExpression self ) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \old expression, <code>self</code>.  By
     * default, this method visits the spec expression of
     * <code>self</code>.
     */
    public void visitJmlOldExpression( 
        /*@ non_null @*/ JmlOldExpression self ) {
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \reach expression, <code>self</code>.  By
     * default, this method visits the store reference expression of
     * <code>self</code>.
     */
    public void visitJmlReachExpression( 
        /*@ non_null @*/ JmlReachExpression self ) {
        if (self.storeRefExpression() != null) {
            self.storeRefExpression().accept(this);
        }
    }

    /**
     * Visits the given \result expression, <code>self</code>.  By
     * default, this method does nothing.
     */
    public void visitJmlResultExpression( JmlResultExpression self ) {
    }

    /**
     * Visits the given set comprehension expression,
     * <code>self</code>.  By default, this method visits boeth
     * predicate and superset predicate of <code>self</code>.
     */
    public void visitJmlSetComprehension( 
        /*@ non_null @*/ JmlSetComprehension self ) {

        //@ assert self.predicate() != null;
	self.predicate().accept(this);
        //@ assert self.supersetPred() != null;
	self.supersetPred().accept(this);
    }

    /**
     * Visits the given spec quantified expression, <code>self</code>.
     * By default, this method visits both predicate and spec
     * expression of <code>self</code>.
     */
    public void visitJmlSpecQuantifiedExpression( 
	JmlSpecQuantifiedExpression self) {
	if (self.hasPredicate())
	    self.predicate().accept(this);
        //@ assert self.specExpression() != null;
	self.specExpression().accept(this);
    }

    /**
     * Visits the given \type expression, <code>self</code>.
     * By default, this method does nothing.
     */
    public void visitJmlTypeExpression( JmlTypeExpression self ) {
    }

    /**
     * Visits the given \typeof expression, <code>self</code>.  By
     * default, this method visits the spec expression of
     * <code>self</code>.
     */
    public void visitJmlTypeOfExpression( 
        /*@ non_null @*/ JmlTypeOfExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Visits the given assignment expression, <code>self</code>.  By
     * default, this method visits both the left and right side
     * expression of <code>self</code>.
     */
    public void visitAssignmentExpression( 
        /*@ non_null @*/ JAssignmentExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Visits the given compound assignment expression,
     * <code>self</code>.  By default, this method visits both the
     * left and right side expression of <code>self</code>.
     */
    public void visitCompoundAssignmentExpression(
	/*@ non_null @*/ JCompoundAssignmentExpression self) {
	visitBinaryExpression(self);
    }

    /**
     * Visits the given conditional expression, <code>self</code>.  By
     * default, this method visits the condition, left and right
     * expressions of <code>self</code>.
     */
    public void visitConditionalExpression( 
        /*@ non_null @*/ JConditionalExpression self ) {
	self.cond().accept(this);
	self.left().accept(this);
	self.right().accept(this);
    }

    /** Visits the given JML relational expression,
     * <code>self</code>. By default, this method visits both the left
     * and right expressions of <code>self</code>. */
    public void visitJmlRelationalExpression(
        /*@ non_null @*/ JmlRelationalExpression self) {
	self.left().accept(this);
	self.right().accept(this);
    }

    /** Visits the given conditional and expression,
     * <code>self</code>. By default, this method visits both the left
     * and right expressions of <code>self</code>. */
    public void	visitConditionalAndExpression( 
            /*@ non_null @*/ JConditionalAndExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given condition or expression,
     * <code>self</code>. By default, this method visits both the left
     * and right expressions of <code>self</code>. */
    public void visitConditionalOrExpression( 
        /*@ non_null @*/ JConditionalOrExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given bitwise expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitBitwiseExpression( 
        /*@ non_null @*/ JBitwiseExpression self ) {
	visitBinaryExpression(self);

    }

    /** Visits the given equality expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitEqualityExpression( 
        /*@ non_null @*/ JEqualityExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given relational expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitRelationalExpression( 
        /*@ non_null @*/ JRelationalExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given instanceof expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>. */
    public void visitInstanceofExpression( 
        /*@ non_null @*/ JInstanceofExpression self ) {
	self.expr().accept(this);
    }
    

    /** Visits the given addition expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitAddExpression( 
        /*@ non_null @*/ JAddExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given minus expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitMinusExpression( 
        /*@ non_null @*/ JMinusExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given multiplication expression,
     * <code>self</code>. By default, this method visits both the left
     * and right expressions of <code>self</code>. */
    public void visitMultExpression( 
        /*@ non_null @*/ JMultExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given division expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitDivideExpression( 
        /*@ non_null @*/ JDivideExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given module expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitModuloExpression( 
        /*@ non_null @*/ JModuloExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given shift expression, <code>self</code>. By
     * default, this method visits both the left and right expressions
     * of <code>self</code>. */
    public void visitShiftExpression( 
        /*@ non_null @*/ JShiftExpression self ) {
	visitBinaryExpression(self);
    }

    /** Visits the given prefix expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>. */
    public void visitPrefixExpression( 
        /*@ non_null @*/ JPrefixExpression self ) {
	self.expr().accept(this);
    }

    /** Visits the given postfix expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>. */
    public void visitPostfixExpression( 
        /*@ non_null @*/ JPostfixExpression self ) {
	self.expr().accept(this);
    }

    /** Visits the given unary expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>. */
    public void visitUnaryExpression( 
        /*@ non_null @*/ JUnaryExpression self ) {
	self.expr().accept(this);
    }

    /** Visits the given cast expression, <code>self</code>. By
     * default, this method visits the expression of
     * <code>self</code>. */
    public void visitCastExpression( 
        /*@ non_null @*/ JCastExpression self ) {
	self.expr().accept(this);
    }

    /** Visits the given unary promition expression,
     * <code>self</code>. By default, this method visits the
     * expression of of <code>self</code>. */
    public void visitUnaryPromoteExpression( 
        /*@ non_null @*/ JUnaryPromote self ) {
	self.expr().accept(this);
    }

    /** Visits the given method expression, <code>self</code>. By
     * default, this method visits both prefix and arguments of
     * <code>self</code>. */
    public void visitMethodCallExpression( 
        /*@ non_null @*/ JMethodCallExpression self ) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
	visitExpressions(self.args());
    }

    /** Visits the given type name expression, <code>self</code>. By
     * default, this method does nothing. */
    public void visitTypeNameExpression( 
        /*@ non_null @*/ JTypeNameExpression self ) {
    }

    /** Visits the given this expression, <code>self</code>. By
     * default, this method does nothing. */
    public void visitThisExpression( 
        /*@ non_null @*/ JThisExpression self ) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
    }

    /** Visits the given super expression, <code>self</code>. By
     * default, this method does nothing. */
    public void visitSuperExpression( 
        /*@ non_null @*/JSuperExpression self ) {
    }

    /** Visits the given class expression, <code>self</code>. By
     * default, this method does nothing. */
    public void visitClassExpression( 
        /*@ non_null @*/ JClassExpression self ) {
    }

    /** Visits the given explicit constructor invocation,
    * <code>self</code>. By default, this method visits bothe prefix
    * and parameters of <code>self</code>. */
    public void visitExplicitConstructorInvocation(
        /*@ non_null @*/ JExplicitConstructorInvocation self) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
	visitExpressions(self.params());
    }

    /** Visits the given array lenth expression, <code>self</code>. By
    * default, this method visits the prefix of <code>self</code>. */
    public void visitArrayLengthExpression( 
        /*@ non_null @*/ JArrayLengthExpression self ) {
	self.prefix().accept(this);
    }

    /** Visits the given array access expression,
    * <code>self</code>. By default, this method visits bith prefix
    * and accessor of <code>self</code>. */
    public void visitArrayAccessExpression( 
        /*@ non_null @*/ JArrayAccessExpression self ) {
	self.prefix().accept(this);
	self.accessor().accept(this);
    }

    /** Visits the given local variable expression,org.multijava.mjc.Main.processTaskQueue
    * <code>self</code>. By default, this method does nothing. */
    public void visitNameExpression( 
        /*@ non_null @*/ JNameExpression self ) {
    }

   /** Visits the given local variable expression,
    * <code>self</code>. By default, this method does nothing. */
    public void visitLocalVariableExpression( 
        /*@ non_null @*/ JLocalVariableExpression self ) {
    }

   /** Visits the given parenthesed expression, <code>self</code>. By
    * default, this method visits the expression of
    * <code>self</code>. */
    public void visitParenthesedExpression( 
        /*@ non_null @*/ JParenthesedExpression self ) {
	self.expr().accept(this);
    }

   /** Visits the given new object expression,
    * <code>self</code>. By default, this method visits both the
    * this expression and parameters of <code>self</code>. */
    public void visitNewObjectExpression( 
        /*@ non_null @*/ JNewObjectExpression self ) {
        if (self.thisExpr() != null) {
            self.thisExpr().accept(this);
        }
	visitExpressions(self.params());
    }

   /** Visits the given new anonymous class expression,
    * <code>self</code>. By default, this method visits the
    * declaration of <code>self</code>. */
    public void visitNewAnonymousClassExpression( 
	/*@ non_null @*/ JNewAnonymousClassExpression self ) {
	self.decl().accept(this);
    }

   /** Visits the given new array expression, <code>self</code>. By
    * default, this method visits both the dimension expression of
    * <code>self</code>. */
    public void visitNewArrayExpression( 
        /*@ non_null @*/ JNewArrayExpression self ) {
	self.dims().accept(this);
    }

   /** Visits the given array dimension and initializer,
    * <code>self</code>. By default, this method visits both the
    * dimension expression and initializer of <code>self</code>. */
    public void visitArrayDimsAndInit(
        /*@ non_null @*/ JArrayDimsAndInits self) {
	visitExpressions(self.dims());
        if (self.init() != null) {
            self.init().accept(this);
        }
    }

   /** Visits the given array initializer, <code>self</code>.  By
    * default, this method visits each elements of
    * <code>self</code>. */
    public void visitArrayInitializer(
        /*@ non_null @*/ JArrayInitializer self) {
	visitExpressions(self.elems());
    }

   /** Visits the given class field expression, <code>self</code>.  By
    * default, this method visits the prefix of <code>self</code> if
    * it is not null. */
    public void visitFieldExpression(
        /*@ non_null@*/ JClassFieldExpression self) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
    }

    // ----------------------------------------------------------------------
    // HELPERS
    // ----------------------------------------------------------------------

    /** Visits the given expressions, <code>exprs</code>. */
    protected void visitExpressions(/*@ non_null @*/ JExpression[] exprs) {
        for (int i = 0; i < exprs.length; i++) {
            if (exprs[i] != null) {
                exprs[i].accept(this);
            }
        }
    }

    /** Visits the binary expressions, <code>exprs</code>. */
    protected void visitBinaryExpression(
        /*@ non_null @*/ JBinaryExpression self) {
	self.left().accept(this);
	self.right().accept(this);
    }
}

