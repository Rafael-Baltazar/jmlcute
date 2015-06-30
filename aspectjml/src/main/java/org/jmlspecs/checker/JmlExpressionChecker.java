/*
 * Copyright (C) 2001-2006 Iowa State University
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
 * $Id: JmlExpressionChecker.java,v 1.31 2006/02/02 16:42:21 chalin Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CAbstractMethodSet;
import org.multijava.mjc.CArrayType;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CField;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CType;
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
import org.multijava.mjc.JLocalVariable;
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
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MJMathModeExpression;
import org.multijava.mjc.MJWarnExpression;
import org.multijava.util.MessageDescription;
import org.multijava.util.compiler.CWarning;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * A visitor class to check privacy (and purity) of JML expressions.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.31 $
 */
public class JmlExpressionChecker extends JmlAbstractVisitor {

    /**
     * Constructs a new instance.
     *
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    private JmlExpressionChecker(CContextType ctx, long privacy) {
        this(ctx, privacy, true);
    }

    /**
     * Constructs a new instance.
     *
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    private JmlExpressionChecker(CContextType ctx, long privacy,
                                 boolean checkPurity ) {
        this.context = ctx;
        this.privacy = privacy;
        this.checkPurity = checkPurity;
    }

    private JmlExpressionChecker(CContextType ctx, long privacy, 
                                 boolean checkPurity,
                                 boolean sideEffectOk) {
        this.context = ctx;
        this.privacy = privacy;
        this.checkPurity = checkPurity;
        this.sideEffectOk = sideEffectOk;
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>expr</code>, in the specification context of visibility,
     * <code>privacy</code>. If there is an error, it is reported
     * using the given context, <code>ctx</code>. The purity check is
     * performed only if the argument <code>checkPurity</code> is
     * true.
     *
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    public static void perform(/*@ non_null @*/ CContextType ctx,
                               long privacy,
                               /*@ non_null @*/ JExpression expr,
                               boolean checkPurity) {
        expr.accept(new JmlExpressionChecker(ctx, privacy, checkPurity));
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>expr</code>, in the specification context of visibility,
     * <code>privacy</code>. If there is an error, it is reported
     * using the given context, <code>ctx</code>.
     *
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    public static void perform(/*@ non_null @*/ CContextType ctx,
                               long privacy,
                               /*@ non_null @*/ JExpression expr) {
        expr.accept(new JmlExpressionChecker(ctx, privacy));
    }

    /**
     * Checks purity of the given expression, <code>expr</code>. If
     * there is an error, it is reported using the given context,
     * <code>ctx</code>.
     */
    public static void perform(/*@ non_null @*/ CContextType ctx,
                               /*@ non_null @*/ JExpression expr) {
        expr.accept(new JmlExpressionChecker(ctx, ACC_PRIVATE));
    }

    /** Checks the given expression allowing side effects. */
    public static void performSideEffectOk(
        /*@ non_null @*/ CContextType ctx,
        /*@ non_null @*/ JExpression expr) {
        expr.accept(new JmlExpressionChecker(
                        ctx, ACC_PRIVATE, false, true));
    }

    // ----------------------------------------------------------------------
    // VISITORS
    // ----------------------------------------------------------------------

    public void visitJmlCodeContract(/*@non_null*/ JmlCodeContract self ) {
    }

    /**
     * Checks visibility of the given expression,
     * <code>self</code>. */
    public void visitJmlDurationExpression(
	JmlDurationExpression self) {
        boolean origCheckPurity = checkPurity;
        checkPurity = false;
	self.expression().accept(this);
        checkPurity = origCheckPurity;
    }

    public void visitJmlPredicate(JmlPredicate self) {
        // if purity/visibility check was not performed as a part of
        // typechecking the given JML predicate, then perform the
        // check now.
        if (!self.purityChecked()) {
            self.setPurityChecked();
            self.specExpression().accept(this);
        }
    }

    public void visitJmlSpecExpression(JmlSpecExpression self) {
        // if purity/visibility check was not performed as a part of
        // typechecking the given spec expression, then perform the
        // check now.
        if (!self.purityChecked()) {
            self.setPurityChecked();
            self.expression().accept(this);
        }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlNotModifiedExpression( 
       JmlNotModifiedExpression self) {
        JmlStoreRef[] storeRefs = self.storeRefList();
        for (int i = 0; i < storeRefs.length; i++) {
            try {
                // At this point, storeRefs[i] has already been
                // typechecked without any error. So, the following
                // call has the effect of only performing visibility
                // check, well with typecheck overhead.
                storeRefs[i].typecheck((CExpressionContextType)context, 
                                       privacy);
            } catch (PositionedError e) {
                context.reportTrouble(e);
            }
        }  
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlNotAssignedExpression( 
       JmlNotAssignedExpression self) {
        JmlStoreRef[] storeRefs = self.storeRefList();
        for (int i = 0; i < storeRefs.length; i++) {
            try {
                // At this point, storeRefs[i] has already been
                // typechecked without any error. So, the following
                // call has the effect of only performing visibility
                // check, well with typecheck overhead.
                storeRefs[i].typecheck((CExpressionContextType)context, 
                                       privacy);
            } catch (PositionedError e) {
                context.reportTrouble(e);
            }
        }  
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlNonNullElementsExpression
	( JmlNonNullElementsExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlElemTypeExpression( JmlElemTypeExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlFreshExpression( JmlFreshExpression self ) {
	JmlSpecExpression[] exprs = self.specExpressionList();
	for (int i = 0; i < exprs.length; i++) 
	    exprs[i].accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlInGroupClause( JmlInGroupClause self ) {
	// no side effects are possible
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlInformalExpression( JmlInformalExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlInvariantForExpression(JmlInvariantForExpression self){
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlIsInitializedExpression( 
        JmlIsInitializedExpression self) {
        checkType(self.referenceType(), self.getTokenReference());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlLabelExpression( JmlLabelExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlLockSetExpression( JmlLockSetExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlMapsIntoClause( JmlMapsIntoClause self ) {
	// no side effects are possible
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlOldExpression( JmlOldExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlPreExpression( JmlPreExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlReachExpression( JmlReachExpression self ) {
        
        // check visibility of spec expression
        self.specExpression().accept(this);

        // check visibility of type
        CType type = self.referenceType();
        if (type != null) {
            checkType(type, self.getTokenReference());
        }

        // check visibility of store reference
        JmlStoreRefExpression storeRef = self.storeRefExpression();
        if (storeRef != null) {
            try {
                storeRef.typecheck((CExpressionContextType)context, 
                                   privacy, type);
            } catch (PositionedError e) {
                context.reportTrouble(e);
            }
        }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlResultExpression( JmlResultExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlSetComprehension( JmlSetComprehension self ) {
        checkType(self.getType(), self.getTokenReference());
        checkType(self.memberType(), self.getTokenReference());
	self.predicate().accept(this);
	self.supersetPred().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlSpaceExpression( JmlSpaceExpression self ) {
	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlSpecQuantifiedExpression( 
	JmlSpecQuantifiedExpression self) {
        JVariableDefinition[] vars = self.quantifiedVarDecls();
        for (int i = 0; i < vars.length; i++)
            vars[i].accept(this);

	if (self.hasPredicate())
	    self.predicate().accept(this);

	self.specExpression().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlVariableDefinition( JmlVariableDefinition self ) {
        checkType(self.getType(), self.getTokenReference());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitVariableDefinition( JVariableDefinition self ) {
        checkType(self.getType(), self.getTokenReference());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlTypeExpression( JmlTypeExpression self ) {
        checkType(self.type(), self.getTokenReference());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlTypeOfExpression( JmlTypeOfExpression self ) {
	self.specExpression().accept(this);
    }


    /**
     * Checks visibility of the given expression,
     * <code>self</code>. */
    public void visitJmlWorkingSpaceExpression(
	JmlWorkingSpaceExpression self) {
        boolean origCheckPurity = checkPurity;
        checkPurity = false;
	self.expression().accept(this);
        checkPurity = origCheckPurity;
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitAssignmentExpression( JAssignmentExpression self ) {
        check(sideEffectOk, self.getTokenReference(), 
              JmlMessages.NO_ASSIGNMENT_EXPRESSION);

        if (sideEffectOk && isModelFieldReference(self.left())) {
            check(false, self.getTokenReference(), 
                  JmlMessages.MODEL_LHS_IN_ASSIGNMENT);
        }
        
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitCompoundAssignmentExpression(
	JCompoundAssignmentExpression self) {
        check(sideEffectOk, self.getTokenReference(), 
              JmlMessages.NO_ASSIGNMENT_EXPRESSION);

        if (sideEffectOk && isModelFieldReference(self.left())) {
            check(false, self.getTokenReference(), 
                  JmlMessages.MODEL_LHS_IN_ASSIGNMENT);
        }

	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitConditionalExpression( JConditionalExpression self ) {
	self.cond().accept(this);
	self.left().accept(this);
	self.right().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitJmlRelationalExpression(JmlRelationalExpression self) {
	self.left().accept(this);
	self.right().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void
	visitConditionalAndExpression( JConditionalAndExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void 
	visitConditionalOrExpression( JConditionalOrExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitBitwiseExpression( JBitwiseExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitEqualityExpression( JEqualityExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitRelationalExpression( JRelationalExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitInstanceofExpression( JInstanceofExpression self ) {
	self.expr().accept(this);

        // check visibility of type, e.g., T in "x instanceof T".
        checkType(self.dest(), self.getTokenReference());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */    
    public void visitAddExpression( JAddExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitMinusExpression( JMinusExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitMultExpression( JMultExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitDivideExpression( JDivideExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitModuloExpression( JModuloExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitShiftExpression( JShiftExpression self ) {
	visitBinaryExpression(self);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitPrefixExpression( JPrefixExpression self ) {
        check(sideEffectOk, self.getTokenReference(), 
              JmlMessages.NO_PREFIX_EXPRESSION);

        if (sideEffectOk && isModelFieldReference(self.expr())) {
            check(false, self.getTokenReference(), 
                  JmlMessages.MODEL_IN_PREFIX_EXPRESSION);
        }

	self.expr().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitPostfixExpression( JPostfixExpression self ) {
        check(sideEffectOk, self.getTokenReference(), 
              JmlMessages.NO_POSTFIX_EXPRESSION);

        if (sideEffectOk && isModelFieldReference(self.expr())) {
            check(false, self.getTokenReference(), 
                  JmlMessages.MODEL_IN_PREFIX_EXPRESSION);
        }

	self.expr().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitUnaryExpression( JUnaryExpression self ) {
	self.expr().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitCastExpression( JCastExpression self ) {
        // check visibility of type, e.g, T in "(T)x".
        checkType(self.getType(), self.getTokenReference());

	self.expr().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitUnaryPromoteExpression( JUnaryPromote self ) {
	self.expr().accept(this);
    }

    /** Checks the given method call expression for visibility and
     * purity violations. */
    public void visitMethodCallExpression( JMethodCallExpression self ) {
	if (self.prefix() != null) {
	    self.prefix().accept(this);
	}

        // check visibility
        check(isVisibilityOk(privacy, self.method().modifiers()),
              self.getTokenReference(), 
              JmlMessages.METHOD2_VISIBILITY,
	      new Object[] {
                self.method().ident(), 
		JmlNode.privacyString( self.method().modifiers() ), 
		JmlNode.privacyString(privacy)} );

        // Pureness of method call is checked only if the
        // command-option --purity (-p) is turned on, and the checking
        // make sense for the particular context, e.g., it is not
        // checked in callable clauses.
        if (Main.jmlOptions.purity() && checkPurity) {
            // is the method "pure"?
            warnPureness(methodPureness(self.method(), self.prefix()),
                         self.getTokenReference(), 
                         self.method().ident());
        }

	visitExpressions(self.args());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitTypeNameExpression( JTypeNameExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitThisExpression( JThisExpression self ) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitSuperExpression( JSuperExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitClassExpression( JClassExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitExplicitConstructorInvocation(
        JExplicitConstructorInvocation self) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }
	visitExpressions(self.params());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitArrayLengthExpression( JArrayLengthExpression self ) {
	self.prefix().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitArrayAccessExpression( JArrayAccessExpression self ) {
	self.prefix().accept(this);
	self.accessor().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitNameExpression( JNameExpression self ) {
        if (self.getPrefix() != null) {
            self.getPrefix().accept(this);
        }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitLocalVariableExpression( JLocalVariableExpression self ) {
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitParenthesedExpression( JParenthesedExpression self ) {
	self.expr().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitNewObjectExpression( JNewObjectExpression self ) {
        // check visibility of type, e.g, T in "new T()".
        checkType(self.getType(), self.getTokenReference());

        if (self.thisExpr() != null) {
            self.thisExpr().accept(this);
        }
	visitExpressions(self.params());
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitNewAnonymousClassExpression( 
	JNewAnonymousClassExpression self ) {
	self.decl().accept(this);

        // !FIXME!privacy! of new anonymous class expression
        // check visibility of type, e.g, T in new T() { ... }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitNewArrayExpression( JNewArrayExpression self ) {
        // check visibility of type, e.g, T in new T[10].
        checkType(self.getType(), self.getTokenReference());

	self.dims().accept(this);
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitArrayDimsAndInit(JArrayDimsAndInits self) {
	visitExpressions(self.dims());
        if (self.init() != null) {
            self.init().accept(this);
        }
    }

    /**
     * Checks visibility (and purity) of the given expression,
     * <code>self</code>. */
    public void visitArrayInitializer(JArrayInitializer self) {
	visitExpressions(self.elems());
    }

    /** Checks the given class field expression for visibility and
     * purity violations. */
    public void visitFieldExpression(JClassFieldExpression self) {
        if (self.prefix() != null) {
            self.prefix().accept(this);
        }

        // check visibility of the field
        CField field = self.getField().getField();
        // not generated one, e.g., this$0?
        if (field.ident().indexOf('$') == -1) { 
            check(isVisibilityOk(privacy, field.modifiers()),
                  self.getTokenReference(), 
                  JmlMessages.FIELD2_VISIBILITY,
		  new Object[] {
                  field.ident(), JmlNode.privacyString( field.modifiers() ), 
				JmlNode.privacyString(privacy) });
        }
    }

    /**
     * Checks visibility (and purity) of the given expression. */
    public void visitWarnExpression( MJWarnExpression self ) {
	self.expr().accept(this);
    }
    
    /**
     * Checks visibility (and purity) of the given expression. */
    public void visitMathModeExpression( MJMathModeExpression self ) {
	self.expr().accept(this);
    }

    // ----------------------------------------------------------------------
    // HELPER METHODS
    // ----------------------------------------------------------------------

    /**
     * Checks visibility (and purity) of the given expressions,
     * <code>expr</code>. */
    protected void visitExpressions(JExpression[] exprs) {
        for (int i = 0; i < exprs.length; i++) {
            if (exprs[i] != null) {
                exprs[i].accept(this);
            }
        }
    }

    /**
     * Checks visibility (and purity) of the given binary expression,
     * <code>expr</code>. */
    protected void visitBinaryExpression(JBinaryExpression expr) {
	expr.left().accept(this);
	expr.right().accept(this);
    }
    
    /**
     * Checks if the condition, <code>cond</code> is true. If not,
     * reports a positioned error.
     */
    private void check(boolean cond, TokenReference tref,
        MessageDescription msg, Object obj1, Object obj2) {
        if (!cond) {
            context.reportTrouble(
                new PositionedError(tref, msg, new Object[] { obj1, obj2 }));
        }
    }

    private void check(boolean cond, TokenReference tref,
        MessageDescription msg, Object[] obj) {
        if (!cond) {
            context.reportTrouble(
                new PositionedError(tref, msg, obj));
        }
    }

    /**
     * Checks if the condition, <code>cond</code> is true. If not,
     * reports a positioned error.
     */
    private void check(boolean cond, TokenReference tref,
        MessageDescription msg, Object obj1) {
        if (!cond) {
            context.reportTrouble(
                new PositionedError(tref, msg, new Object[] { obj1 }));
        }
    }

    /**
     * Checks if the condition, <code>cond</code> is true. If not,
     * reports a positioned error.
     */
    private void check(boolean cond, TokenReference tref,
        MessageDescription msg) {
        if (!cond) {
            context.reportTrouble(
                new PositionedError(tref, msg, null));
        }
    }
    
    /**
     * Produce a caution message about method pureness if the
     * argument, <code>cond</code>, is -1. If <code>cond</code> is 0,
     * produce a warning message instead; otherwise, do nothing. */
    private void warnPureness(int cond, TokenReference tref, Object obj) {
        if (cond > 0) {
            return;
        }
        else if(cond == 0){
        	 context.reportTrouble(new CWarning(tref,
                     JmlMessages.METHOD_MAY_NOT_PURE, obj));
        }
        else if(cond == -1){
       	 context.reportTrouble(new PositionedError(tref,
                    JmlMessages.METHOD_NOT_PURE, obj));
       }
        
//        context.reportTrouble(new CWarning(tref,
//                                           (cond == 0) ?
//                                           JmlMessages.METHOD_MAY_NOT_PURE
//                                           : JmlMessages.METHOD_NOT_PURE,
//                                           obj));
    }

    /**
     * Returns true if a member (field or method) with the given
     * modifiers, <code>modifiers</code>, can be used in a
     * specification context of the visibility, <code>privacy</code>.
     *
     * <pre><jml>
     * requires privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    public static boolean isVisibilityOk(long privacy, long modifiers) { 
	if(privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC) {
            return hasFlag(modifiers, ACC_PUBLIC | ACC_SPEC_PUBLIC);
	} else if(privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED) {
            return hasFlag(modifiers, ACC_PUBLIC | ACC_SPEC_PUBLIC 
                           | ACC_PROTECTED | ACC_SPEC_PROTECTED);
	} else if(privacy == 0) { // default, i.e., package
            return !hasFlag(modifiers, ACC_PRIVATE)
                || hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_SPEC_PROTECTED);
	} else if(privacy == ACC_PRIVATE) {
            return true;
	}

        return false;
    }

    /**
     * Checks the visibility of the given type, <code>type</code>. If
     * the given type is an array type, the visibility of its base
     * type is checked. For a nested type, also checks the owner
     * type's visibility. If there is a visibility violation, throw an
     * error message composed using the given token reference,
     * <code>ref</code>.
     */
    private void checkType(/*@ non_null @*/ CType type, 
                           /*@ non_null @*/ TokenReference ref) {
        CType btype = getBaseType(type);
        if (btype instanceof CClassType) {
            checkTypeHelper(btype.getCClass(), ref);
        }
    }

    /**
     * Checks the visibility of the given class,
     * <code>clazz</code>. For a nested class, also checks the owner
     * class's visibility. If there is a visibility violation, throw
     * an error message composed using the given token reference,
     * <code>ref</code>.
     */
    private void checkTypeHelper(/*@ non_null @*/ CClass clazz, 
                                 /*@ non_null @*/ TokenReference ref) {
        CClass owner = clazz.owner();
        if (owner != null) {
            checkTypeHelper(owner, ref);
            check(isVisibilityOk(privacy, clazz.modifiers()),
                  ref,
                  JmlMessages.TYPE2_VISIBILITY,
		  new Object[] {
                  clazz.qualifiedName().replace('$', '.'),
                  JmlNode.privacyString( clazz.modifiers() ),
                  JmlNode.privacyString(privacy)} );
        }
    }

    /**
     * Returns the ultimate base type if the given type,
     * <code>type</code>, is an array type. Otherwise, returns the
     * type itself.
     */
    private /*@ non_null @*/ CType getBaseType(/*@ non_null @*/ CType type) {
        if (type instanceof CArrayType) {
            return getBaseType(((CArrayType)type).getBaseType());
        } else {
            return type;
        }
    }


    /**
     * Returns 1 if the given method, <code>meth</code>, is a pure
     * method. A method is pure if it is annoted with the JML
     * <code>pure</code> modifier or its owner (a class or an
     * interface) is declared as pure. Returns -1 if the given method
     * is not pure; returns 0 if it can not be determined, e.g., no
     * source code is available.
     */
    private int methodPureness(/*@ non_null @*/ CMethod meth,
			       /*@ non_null @*/ JExpression prefix) 
    {
	CClass receiver = null;
        if (meth instanceof JmlSourceMethod) {
	    if (prefix != null) {
		receiver = prefix.getType().getCClass();
	    } else {
		// when prefix is null, then the method must be static
		// and so cannot override (see JMethodCallExpression).
		return ((JmlSourceMethod)meth).isPure() ? 1 : -1;
	    }
	    if (meth.receiverType().getCClass().equals(receiver)) {
		return ((JmlSourceMethod)meth).isPure() ? 1 : -1;
	    } else if (receiver instanceof JmlSourceClass) {
		JmlSourceClass receiverClass = (JmlSourceClass) receiver;
		CMethodSet mset = 
		    receiverClass.lookupJMLMethodsWithSameSig(meth);
		CAbstractMethodSet.Iterator iter = mset.iterator();
		while (iter.hasNext()) {
		    CMethod nextMeth = iter.next();
		    if ((nextMeth instanceof JmlSourceMethod) &&
			((JmlSourceMethod) nextMeth).isPure()) {
			return 1;
		    } 
		}
		return -1;
	    } else {
		return ((JmlSourceMethod)meth).isPure() ? 1 : -1;
	    }
        }
        return 0;
    }

    /**
     * Returns <code>true</code> if the given expression,
     * <code>expr</code> is a reference to a model field.
     */
    private static /*@ pure @*/ boolean isModelFieldReference(
        JExpression expr) {
        if (expr instanceof JClassFieldExpression) {
            CFieldAccessor field = ((JClassFieldExpression)expr).getField();
            return (field instanceof JmlModifiable) 
                && ((JmlModifiable) field).isModel();
        } else if (expr instanceof JLocalVariableExpression) {
            JLocalVariable var = ((JLocalVariableExpression)expr).variable();
	    long modifiers = var.modifiers();
	    return hasFlag(modifiers, ACC_MODEL);
        }
        return false;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** The context with which to report error if an error is found
     * while checking visibility and purity. */
    private /*@ non_null @*/ CContextType context;

    /** The visibility of specification context against which JML
     * expressions are checked for visibility.
     *
     * <pre><jml>
     * private invariant privacy == ACC_PUBLIC || privacy == ACC_SPEC_PUBLIC
     *   || privacy == ACC_PROTECTED || privacy == ACC_SPEC_PROTECTED
     *   || privacy == ACC_PRIVATE 
     *   || privacy == 0;
     * </jml></pre>
     */
    private long privacy;

    /** Indicates whether to check purity or not. For a particular
     * context such as accessible clause and callable clause, the
     * purity check should not be performed. */
    private boolean checkPurity;

    /** Indicates if side effects are ok. E.g., in the debug statement. */
    private boolean sideEffectOk = false;
}

