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
 * $Id: JmlVisitorNI.java,v 1.29 2007/04/09 22:47:43 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;

/**
 * Implementation of Visitor Design Pattern for KJC.
 *
 * Suggested from: Max R. Andersen(max@cs.auc.dk)
 * !CONVERT! use open classes
 */
public class JmlVisitorNI implements JmlVisitor {

    protected void imp(String method, Object self) 
    {
	String msg = "NOT IMPLEMENTED: method JmlVisitorNI." + method 
	    + " needs to be overridden (" 
	    + self.getClass() + ")";
	System.err.println(msg);

	/* The message printed above is not that helpful. It would be much
	 * better if we could inform the specifier of the specification
	 * construct that caused the problem.  That is what I do below by
	 * having a PositionedError be thrown.  Actually, I don't want to have
	 * to change the signature of this method (by adding a throws
	 * org.multijava.util.compiler.PositionedError because that would mean
	 * changing the signature of all of the visitJml* methods.  Hence we
	 * will wrap our PostiontionedError in a unchecked exception ...
	 */
	if(self instanceof org.multijava.mjc.JExpression) {
	    org.multijava.util.MessageDescription m = 
		new org.multijava.util.MessageDescription(msg, null,
							  org.multijava.util.MessageDescription.LVL_ERROR);
	    try {
		((org.multijava.mjc.JExpression) self).check(null, false, m);
	    } catch(Exception ex) {
		throw new ArithmeticException(ex.toString());
	    }
	}
    }
	
    public void visitJmlAbruptSpecBody( JmlAbruptSpecBody self ) { imp("visitJmlAbruptSpecBody",self); }
    public void visitJmlAbruptSpecCase( JmlAbruptSpecCase self ) { imp("visitJmlAbruptSpecCase",self); }
    public void visitJmlAccessibleClause( JmlAccessibleClause self ) { imp("visitJmlAccessibleClause",self); }
    public void visitJmlAssertStatement( JmlAssertStatement self ) { imp("visitJmlAssertStatement",self); }
    public void visitJmlAssignableClause( JmlAssignableClause self ) { imp("visitJmlAssignableClause",self); }
    public void visitJmlAssumeStatement( JmlAssumeStatement self ) { imp("visitJmlAssumeStatement",self); }
    public void visitJmlAxiom( JmlAxiom self ) { imp("visitJmlAxiom",self); }
    public void visitJmlBehaviorSpec( JmlBehaviorSpec self ) { imp("visitJmlBehaviorSpec",self); }
    public void visitJmlBreaksClause( JmlBreaksClause self ) { imp("visitJmlBreaksClause",self); }
    public void visitJmlCallableClause( JmlCallableClause self ) { imp("visitJmlCallableClause",self); }
    public void visitJmlCapturesClause( JmlCapturesClause self ) { imp("visitJmlCapturesClause",self); }
    public void visitJmlClassBlock( JmlClassBlock self ) { imp("visitJmlClassBlock",self); }
    public void visitJmlClassDeclaration( JmlClassDeclaration self ) { imp("visitJmlClassDeclaration",self); }
    public void visitJmlClassOrGFImport( JmlClassOrGFImport self ) { imp("visitJmlClassOrGFImport",self); }
    public void visitJmlCodeContract( JmlCodeContract self ) { imp("visitJmlCodeContract",self); }
    public void visitJmlCompilationUnit( JmlCompilationUnit self ) { imp("visitJmlCompilationUnit",self); }
    public void visitJmlConstraint( JmlConstraint self ) { imp("visitJmlConstraint",self); }
    public void visitJmlConstructorDeclaration( JmlConstructorDeclaration self ) { imp("visitJmlConstructorDeclaration",self); }
    public void visitJmlConstructorName( JmlConstructorName self ) { imp("visitJmlConstructorName",self); }
    public void visitJmlContinuesClause( JmlContinuesClause self ) { imp("visitJmlContinuesClause",self); }
	public void visitJmlDeclaration( JmlDeclaration self ) { imp("visitJmlDeclaration",self); }
    public void visitJmlDivergesClause( JmlDivergesClause self ) { imp("visitJmlDivergesClause",self); }
    public void visitJmlDebugStatement( JmlDebugStatement self ) { imp("visitJmlDebugStatement",self); }
    public void visitJmlDurationClause( JmlDurationClause self ) { imp("visitJmlDurationClause",self); }
    public void visitJmlDurationExpression( JmlDurationExpression self ) { imp("visitJmlDurationExpression",self); }
    public void visitJmlElemTypeExpression( JmlElemTypeExpression self ) { imp("visitJmlElemTypeExpression",self); }
    public void visitJmlEnsuresClause( JmlEnsuresClause self ) { imp("visitJmlEnsuresClause",self); }
    public void visitJmlExample( JmlExample self ) { imp("visitJmlExample",self); }
    public void visitJmlExceptionalBehaviorSpec( JmlExceptionalBehaviorSpec self ) { imp("visitJmlExceptionalBehaviorSpec",self); }
    public void visitJmlExceptionalExample( JmlExceptionalExample self ) { imp("visitJmlExceptionalExample",self); }
    public void visitJmlExceptionalSpecBody( JmlExceptionalSpecBody self ) { imp("visitJmlExceptionalSpecBody",self); }
    public void visitJmlExceptionalSpecCase( JmlExceptionalSpecCase self ) { imp("visitJmlExceptionalSpecCase",self); }
	public void visitJmlExpression( JmlExpression self ) { imp("visitJmlExpression",self); }
    public void visitJmlExtendingSpecification( JmlExtendingSpecification self ) { imp("visitJmlExtendingSpecification",self); }
    public void visitJmlFieldDeclaration( JmlFieldDeclaration self ) { imp("visitJmlFieldDeclaration",self); }
    public void visitJmlForAllVarDecl( JmlForAllVarDecl self ) { imp("visitJmlForAllVarDecl",self); }
    public void visitJmlFormalParameter( JmlFormalParameter self ) { imp("visitJmlForAllVarDecl",self); }
    public void visitJmlFreshExpression( JmlFreshExpression self ) { imp("visitJmlFreshExpression",self); }
	public void visitJmlGeneralSpecCase( JmlGeneralSpecCase self ) { imp("visitJmlGeneralSpecCase",self); }
    public void visitJmlGenericSpecBody( JmlGenericSpecBody self ) { imp("visitJmlGenericSpecBody",self); }
    public void visitJmlGenericSpecCase( JmlGenericSpecCase self ) { imp("visitJmlGenericSpecCase",self); }
    public void visitJmlGuardedStatement( JmlGuardedStatement self ) { imp("visitJmlGuardedStatement",self); }
    public void visitJmlHenceByStatement( JmlHenceByStatement self ) { imp("visitJmlHenceByStatement",self); }
    public void visitJmlInGroupClause( JmlInGroupClause self ) { imp("visitJmlInGroupClause",self); }
    public void visitJmlInformalExpression( JmlInformalExpression self ) { imp("visitJmlInformalExpression",self); }
    public void visitJmlInformalStoreRef( JmlInformalStoreRef self ) { imp("visitJmlInformalStoreRef",self); }
    public void visitJmlInitiallyVarAssertion( JmlInitiallyVarAssertion self ) { imp("visitJmlInitiallyVarAssertion",self); }
    public void visitJmlInterfaceDeclaration( JmlInterfaceDeclaration self ) { imp("visitJmlInterfaceDeclaration",self); }
    public void visitJmlInvariant( JmlInvariant self ) { imp("visitJmlInvariant",self); }
    public void visitJmlInvariantForExpression( JmlInvariantForExpression self ) { imp("visitJmlInvariantForExpression",self); }
    public void visitJmlInvariantStatement( JmlInvariantStatement self ) { imp("visitJmlInvariantStatement",self); }
    public void visitJmlIsInitializedExpression( JmlIsInitializedExpression self ) { imp("visitJmlIsInitializedExpression",self); }
    public void visitJmlLabelExpression( JmlLabelExpression self ) { imp("visitJmlLabelExpression",self); }
    public void visitJmlLetVarDecl( JmlLetVarDecl self ) { imp("visitJmlLetVarDecl",self); }
    public void visitJmlLockSetExpression( JmlLockSetExpression self ) { imp("visitJmlLockSetExpression",self); }
    public void visitJmlLoopInvariant( JmlLoopInvariant self ) { imp("visitJmlLoopInvariant",self); }
    public void visitJmlLoopStatement( JmlLoopStatement self ) { imp("visitJmlLoopStatement",self); }
    public void visitJmlMapsIntoClause( JmlMapsIntoClause self ) { imp("visitJmlMapsIntoClause",self); }
    public void visitJmlMaxExpression( JmlMaxExpression self ) { imp("visitJmlMaxExpression",self); }
    public void visitJmlMeasuredClause( JmlMeasuredClause self ) { imp("visitJmlMeasuredClause",self); }
    public void visitJmlMethodDeclaration( JmlMethodDeclaration self ) { imp("visitJmlMethodDeclaration",self); }
    public void visitJmlMethodName( JmlMethodName self ) { imp("visitJmlMethodName",self); }
    public void visitJmlMethodNameList( JmlMethodNameList self ) { imp("visitJmlMethodNameList",self); }
	public void visitJmlMethodSpecification( JmlMethodSpecification self ) { imp("visitJmlMethodSpecification",self); }
    public void visitJmlModelProgram( JmlModelProgram self ) { imp("visitJmlModelProgram",self); }
    public void visitJmlMonitorsForVarAssertion( JmlMonitorsForVarAssertion self ) { imp("visitJmlMonitorsForVarAssertion",self); }
    public void visitJmlName( JmlName self ) { imp("visitJmlName",self); }
	public void visitJmlNode( JmlNode self ) { imp("visitJmlNode",self); }
    public void visitJmlNonNullElementsExpression( 
         JmlNonNullElementsExpression self ) { imp("visitJmlNonNullElementsExpression",self); }
    public void visitJmlAssignmentStatement( JmlAssignmentStatement self ) { imp("visitJmlAssignmentStatement",self); }
    public void visitJmlNondetChoiceStatement( JmlNondetChoiceStatement self ) { imp("visitJmlNondetChoiceStatement",self); }
    public void visitJmlNondetIfStatement( JmlNondetIfStatement self ) { imp("visitJmlNondetIfStatement",self); }
    public void visitJmlNormalBehaviorSpec( JmlNormalBehaviorSpec self ) { imp("visitJmlNormalBehaviorSpec",self); }
    public void visitJmlNormalExample( JmlNormalExample self ) { imp("visitJmlNormalExample",self); }
    public void visitJmlNormalSpecBody( JmlNormalSpecBody self ) { imp("visitJmlNormalSpecBody",self); }
    public void visitJmlNormalSpecCase( JmlNormalSpecCase self ) { imp("visitJmlNormalSpecCase",self); }
    public void visitJmlNotAssignedExpression( JmlNotAssignedExpression self ) { imp("visitJmlNotAssignedExpression",self); }
    public void visitJmlNotModifiedExpression( JmlNotModifiedExpression self ) { imp("visitJmlNotModifiedExpression",self); }
    public void visitJmlOnlyAccessedExpression( JmlOnlyAccessedExpression self ) { imp("visitJmlOnlyAccessedExpression",self); }
    public void visitJmlOnlyAssignedExpression( JmlOnlyAssignedExpression self ) { imp("visitJmlOnlyAssignedExpression",self); }
    public void visitJmlOnlyCalledExpression( JmlOnlyCalledExpression self ) { imp("visitJmlOnlyCalledExpression",self); }
    public void visitJmlOnlyCapturedExpression( JmlOnlyCapturedExpression self ) { imp("visitJmlOnlyCapturedExpression",self); }
    public void visitJmlOldExpression( JmlOldExpression self ) { imp("visitJmlOldExpression",self); }
    public void visitJmlPackageImport( JmlPackageImport self ) { imp("visitJmlPackageImport",self); }
    public void visitJmlPredicate( JmlPredicate self ) { imp("visitJmlPredicate",self); }
    public void visitJmlPredicateKeyword( JmlPredicateKeyword self ) { imp("visitJmlPredicateKeyword",self); }
    public void visitJmlPreExpression( JmlPreExpression self ) { imp("visitJmlPreExpression",self); }
    public void visitJmlReachExpression( JmlReachExpression self ) { imp("visitJmlReachExpression",self); }
    public void visitJmlReadableIfVarAssertion( JmlReadableIfVarAssertion self ) { imp("visitJmlReadableIfVarAssertion",self); }
    public void visitJmlWritableIfVarAssertion( JmlWritableIfVarAssertion self ) { imp("visitJmlWritableIfVarAssertion",self); }
    public void visitJmlRedundantSpec( JmlRedundantSpec self ) { imp("visitJmlRedundantSpec",self); }
    public void visitJmlRefinePrefix( JmlRefinePrefix self ) { imp("visitJmlRefinePrefix",self); }
    public void visitJmlRelationalExpression( JmlRelationalExpression self ) { imp("visitJmlRelationalExpression",self); }
    public void visitJmlRepresentsDecl( JmlRepresentsDecl self ) { imp("visitJmlRepresentsDecl",self); }
    public void visitJmlRequiresClause( JmlRequiresClause self ) { imp("visitJmlRequiresClause",self); }
    public void visitJmlResultExpression( JmlResultExpression self ) { imp("visitJmlResultExpression",self); }
    public void visitJmlReturnsClause( JmlReturnsClause self ) { imp("visitJmlReturnsClause",self); }
    public void visitJmlSetComprehension( JmlSetComprehension self ) { imp("visitJmlSetComprehension",self); }
    public void visitJmlSetStatement( JmlSetStatement self ) { imp("visitJmlSetStatement",self); }
    public void visitJmlRefiningStatement( JmlRefiningStatement self ) { imp("visitJmlRefiningStatement",self); }
    public void visitJmlSignalsOnlyClause( JmlSignalsOnlyClause self ) { imp("visitJmlSignalsOnlyClause",self); }
    public void visitJmlSignalsClause( JmlSignalsClause self ) { imp("visitJmlSignalsClause",self); }
	public void visitJmlSpecBody( JmlSpecBody self ) { imp("visitJmlSpecBody",self); }
    public void visitJmlSpaceExpression( JmlSpaceExpression self ) { imp("visitJmlSpaceExpression",self); }
    public void visitJmlSpecExpression( JmlSpecExpression self ) { imp("visitJmlSpecExpression",self); }
    public void visitJmlSpecQuantifiedExpression( JmlSpecQuantifiedExpression self ) { imp("visitJmlSpecQuantifiedExpression",self); }
    public void visitJmlSpecStatement( JmlSpecStatement self ) { imp("visitJmlSpecStatement",self); }
    public void visitJmlSpecification( JmlSpecification self ) { imp("visitJmlSpecification",self); }
	public void visitJmlSpecVarDecl( JmlSpecVarDecl self ) { imp("visitJmlSpecVarDecl",self); }
	public void visitJmlStoreRef( JmlStoreRef self ) { imp("visitJmlStoreRef",self); }
    public void visitJmlStoreRefExpression( JmlStoreRefExpression self ) { imp("visitJmlStoreRefExpression",self); }
    public void visitJmlStoreRefKeyword( JmlStoreRefKeyword self ) { imp("visitJmlStoreRefKeyword",self); }
    public void visitJmlTypeExpression( JmlTypeExpression self ) { imp("visitJmlTypeExpression",self); }
    public void visitJmlTypeOfExpression( JmlTypeOfExpression self ) { imp("visitJmlTypeOfExpression",self); }
    public void visitJmlUnreachableStatement( JmlUnreachableStatement self ) { imp("visitJmlUnreachableStatement",self); }
    public void visitJmlVariantFunction( JmlVariantFunction self ) { imp("visitJmlVariantFunction",self); }
    public void visitJmlVariableDefinition( JmlVariableDefinition self ) { imp("visitJmlVariableDefinition",self); }
    public void visitJmlWhenClause( JmlWhenClause self ) { imp("visitJmlWhenClause",self); }
    public void visitJmlWorkingSpaceClause( JmlWorkingSpaceClause self ) { imp("visitJmlWorkingSpaceClause",self); }
    public void visitJmlWorkingSpaceExpression( JmlWorkingSpaceExpression self ) { imp("visitJmlWorkingSpaceExpression",self); }
	
	// ----------------------------------------------------------------------
    // COMPILATION UNIT
    // ----------------------------------------------------------------------

    /**
     * visits a compilation unit
     */
    public void visitCompilationUnit( JCompilationUnit self ) { imp("visitCompilationUnit",self); }

    // ----------------------------------------------------------------------
    // TYPE DECLARATION
    // ----------------------------------------------------------------------

    /**
     * visits a class declaration
     */
    public void visitClassDeclaration( JClassDeclaration self ) { imp("visitClassDeclaration",self); }

    /**
     * visits an interface declaration
     */
    public void visitInterfaceDeclaration( JInterfaceDeclaration self ) { imp("visitInterfaceDeclaration",self); }

    /**
     * visits a generic function anchor
     */
    public void visitGenericFunctionDecl( MJGenericFunctionDecl self ) { imp("visitGenericFunctionDecl",self); }

    // ----------------------------------------------------------------------
    // METHODS AND FIELDS
    // ----------------------------------------------------------------------

    /**
     * visits a field declaration
     */
    public void visitFieldDeclaration( JFieldDeclaration self ) { imp("visitFieldDeclaration",self); }

    /**
     * visits a method declaration
     */
    public void visitMethodDeclaration( JMethodDeclaration self ) { imp("visitMethodDeclaration",self); }

    /**
     * visits an initializer declaration
     */
    public void visitInitializerDeclaration( JInitializerDeclaration self ) { imp("visitInitializerDeclaration",self); }

    /**
     * visits an external method declaration
     */
    public void visitTopLevelMethodDeclaration( MJTopLevelMethodDeclaration self ) { imp("visitTopLevelMethodDeclaration",self); }

    /**
     * visits a constructor declaration
     */
    public void visitConstructorDeclaration( JConstructorDeclaration self ) { imp("visitConstructorDeclaration",self); }

    // ----------------------------------------------------------------------
    // STATEMENTS
    // ----------------------------------------------------------------------

    /** Visits the given assert statement. */
    public void visitAssertStatement( JAssertStatement self ) {
        imp("visitAssertStatement", self);
    }

    /**
     * visits a while statement
     */
    public void visitWhileStatement( JWhileStatement self ) { imp("visitWhileStatement",self); }

    /**
     * visits a variable declaration statement
     */
    public void visitVariableDeclarationStatement(JVariableDeclarationStatement self) { imp("visitVariableDeclarationStatement",self); }

    /**
     * visits a variable declaration statement
     */
    public void visitVariableDefinition( JVariableDefinition self ) { imp("visitVariableDefinition",self); }

    /**
     * visits a try-catch statement
     */
    public void visitTryCatchStatement( JTryCatchStatement self ) { imp("visitTryCatchStatement",self); }

    /**
     * visits a try-finally statement
     */
    public void visitTryFinallyStatement( JTryFinallyStatement self ) { imp("visitTryFinallyStatement",self); }

    /**
     * visits a throw statement
     */
    public void visitThrowStatement( JThrowStatement self ) { imp("visitThrowStatement",self); }

    /**
     * visits a synchronized statement
     */
    public void visitSynchronizedStatement( JSynchronizedStatement self ) { imp("visitSynchronizedStatement",self); }

    /**
     * visits a switch statement
     */
    public void visitSwitchStatement( JSwitchStatement self ) { imp("visitSwitchStatement",self); }

    /**
     * visits a return statement
     */
    public void visitReturnStatement( JReturnStatement self ) { imp("visitReturnStatement",self); }

    /**
     * visits a labeled statement
     */
    public void visitLabeledStatement( JLabeledStatement self ) { imp("visitLabeledStatement",self); }

    /**
     * visits a if statement
     */
    public void visitIfStatement( JIfStatement self ) { imp("visitIfStatement",self); }

    /**
     * visits a for statement
     */
    public void visitForStatement( JForStatement self ) { imp("visitForStatement",self); }

    /**
     * visits a compound statement
     */
    public void visitCompoundStatement( JCompoundStatement self ) { imp("visitCompoundStatement",self); }

    /**
     * visits an expression statement
     */
    public void visitExpressionStatement( JExpressionStatement self ) { imp("visitExpressionStatement",self); }

    /**
     * visits an expression list statement
     */
    public void visitExpressionListStatement( JExpressionListStatement self ) { imp("visitExpressionListStatement",self); }

    /**
     * visits a empty statement
     */
    public void visitEmptyStatement( JEmptyStatement self ) { imp("visitEmptyStatement",self); }

    /**
     * visits a do statement
     */
    public void visitDoStatement( JDoStatement self ) { imp("visitDoStatement",self); }

    /**
     * visits a continue statement
     */
    public void visitContinueStatement( JContinueStatement self ) { imp("visitContinueStatement",self); }

    /**
     * visits a break statement
     */
    public void visitBreakStatement( JBreakStatement self ) { imp("visitBreakStatement",self); }

    /**
     * visits an expression statement
     */
    public void visitBlockStatement( JBlock self ) { imp("visitBlockStatement",self); }

    /**
     * visits a constructor block
     */
    public void visitConstructorBlock( JConstructorBlock self ) { imp("visitConstructorBlock",self); }
    /**
     * visits a class block (initializer)
     */
    public void visitClassBlock( JClassBlock self ) { imp("visitClassBlock",self); }

    /**
     * visits a type declaration statement
     */
    public void visitTypeDeclarationStatement( JTypeDeclarationStatement self ) { imp("visitTypeDeclarationStatement",self); }

    // ----------------------------------------------------------------------
    // EXPRESSION
    // ----------------------------------------------------------------------

    /**
     * visits an unary expression
     */
    public void visitUnaryExpression( JUnaryExpression self ) { imp("visitUnaryExpression",self); }

    /**
     * visits a type name expression
     */
    public void visitTypeNameExpression( JTypeNameExpression self ) { imp("visitTypeNameExpression",self); }

    /**
     * visits a this expression
     */
    public void visitThisExpression( JThisExpression self ) { imp("visitThisExpression",self); }

    /**
     * visits a super expression
     */
    public void visitSuperExpression( JSuperExpression self ) { imp("visitSuperExpression",self); }

    /**
     * visits a shift expression
     */
    public void visitShiftExpression( JShiftExpression self ) { imp("visitShiftExpression",self); }

    /**
     * visits a shift expressiona
     */
    public void visitRelationalExpression( JRelationalExpression self ) { imp("visitRelationalExpression",self); }

    /**
     * visits a prefix expression
     */
    public void visitPrefixExpression( JPrefixExpression self ) { imp("visitPrefixExpression",self); }

    /**
     * visits a postfix expression
     */
    public void visitPostfixExpression( JPostfixExpression self ) { imp("visitPostfixExpression",self); }

    /**
     * visits a parenthesed expression
     */
    public void visitParenthesedExpression( JParenthesedExpression self ) { imp("visitParenthesedExpression",self); }

    /**
     * visits an object allocator expression
     */
    public void visitNewObjectExpression( JNewObjectExpression self ) { imp("visitNewObjectExpression",self); }

    /**
     * visits an object allocator expression for an anonymous class
     */
    public void visitNewAnonymousClassExpression( JNewAnonymousClassExpression self ) { imp("visitNewAnonymousClassExpression",self); }

    /**
     * visits an array allocator expression
     */
    public void visitNewArrayExpression( JNewArrayExpression self ) { imp("visitNewArrayExpression",self); }

    /**
     * visits a name expression
     */
    public void visitNameExpression( JNameExpression self ) { imp("visitNameExpression",self); }

    /**
     * visits an add expression
     */
    public void visitAddExpression( JAddExpression self ) { imp("visitAddExpression",self); }

    /**
     * visits a boolean AND expression
     */
    public void visitConditionalAndExpression( JConditionalAndExpression self ) { imp("visitConditionalAndExpression",self); }

    /**
     * visits a boolean OR expression
     */
    public void visitConditionalOrExpression( JConditionalOrExpression self ) { imp("visitConditionalOrExpression",self); }

    /**
     * visits a divide expression
     */
    public void visitDivideExpression( JDivideExpression self ) { imp("visitDivideExpression",self); }

    /**
     * visits a minus expression
     */
    public void visitMinusExpression( JMinusExpression self ) { imp("visitMinusExpression",self); }

    /**
     * visits a modulo division expression
     */
    public void visitModuloExpression( JModuloExpression self ) { imp("visitModuloExpression",self); }

    /**
     * visits a multiplication expression
     */
    public void visitMultExpression( JMultExpression self ) { imp("visitMultExpression",self); }

    /**
     * visits a method call expression
     */
    public void visitMethodCallExpression( JMethodCallExpression self ) { imp("visitMethodCallExpression",self); }
    /**
     * visits a local variable expression
     */
    public void visitLocalVariableExpression( JLocalVariableExpression self ) { imp("visitLocalVariableExpression",self); }

    /**
     * visits an instanceof expression
     */
    public void visitInstanceofExpression( JInstanceofExpression self ) { imp("visitInstanceofExpression",self); }

    /**
     * visits an equality expression
     */
    public void visitEqualityExpression( JEqualityExpression self ) { imp("visitEqualityExpression",self); }

    /**
     * visits a conditional expression
     */
    public void visitConditionalExpression( JConditionalExpression self ) { imp("visitConditionalExpression",self); }

    /**
     * visits a compound expression
     */
    public void visitCompoundAssignmentExpression(JCompoundAssignmentExpression self) { imp("visitCompoundAssignmentExpression",self); }
    /**
     * visits a field expression
     */
    public void visitFieldExpression( JClassFieldExpression self ) { imp("visitFieldExpression",self); }

    /**
     * visits a class expression
     */
    public void visitClassExpression( JClassExpression self ) { imp("visitClassExpression",self); }

    /**
     * visits a cast expression
     */
    public void visitCastExpression( JCastExpression self ) { imp("visitCastExpression",self); }

    /**
     * visits a cast expression
     */
    public void visitUnaryPromoteExpression( JUnaryPromote self ) { imp("visitUnaryPromoteExpression",self); }

    /**
     * visits a compound assignment expression
     */
    public void visitBitwiseExpression( JBitwiseExpression self ) { imp("visitBitwiseExpression",self); }
	
    /**
     * visits an assignment expression
     */
    public void visitAssignmentExpression( JAssignmentExpression self ) { imp("visitAssignmentExpression",self); }

    /**
     * visits an array length expression
     */
    public void visitArrayLengthExpression(JArrayLengthExpression self ) { imp("visitArrayLengthExpression",self); }

    /**
     * visits an array access expression
     */
    public void visitArrayAccessExpression( JArrayAccessExpression self ) { imp("visitArrayAccessExpression",self); }

    // ----------------------------------------------------------------------
    // OTHERS
    // ----------------------------------------------------------------------

    /**
     * visits a switch label
     */
    public void visitSwitchLabel( JSwitchLabel self ) { imp("visitSwitchLabel",self); }

    /**
     * visits a switch group
     */
    public void visitSwitchGroup( JSwitchGroup self ) { imp("visitSwitchGroup",self); }

    /**
     * visits a catch clause
     */
    public void visitCatchClause( JCatchClause self ) { imp("visitCatchClause",self); }

    /**
     * visits a boolean literal
     */
    public void visitBooleanLiteral( JBooleanLiteral self ) { imp("visitBooleanLiteral",self); }

    /**
     * visits a character literal
     */
    public void visitCharLiteral( JCharLiteral self ) { imp("visitCharLiteral",self); }

    /**
     * prints an ordinal literal
     */
    public void visitOrdinalLiteral( JOrdinalLiteral self ) { imp("visitOrdinalLiteral",self); }

    /**
     * prints a real literal
     */
    public void visitRealLiteral( JRealLiteral self ) { imp("visitRealLiteral",self); }

    /**
     * visits a string literal
     */
    public void visitStringLiteral( JStringLiteral self ) { imp("visitStringLiteral",self); }

    /**
     * visits a null literal
     */
    public void visitNullLiteral( JNullLiteral self ) { imp("visitNullLiteral",self); }

    /**
     * visits a package name declaration
     */
    public void visitPackageName( JPackageName self ) { imp("visitPackageName",self); }

    /**
     * visits a package import declaration
     */
    public void visitPackageImport( JPackageImport self ) { imp("visitPackageImport",self); }

    /**
     * visits a class import declaration
     */
    public void visitClassOrGFImport( JClassOrGFImport self ) { imp("visitClassOrGFImport",self); }

    /**
     * visits a formal parameter
     */
    public void visitFormalParameters( JFormalParameter self ) { imp("visitFormalParameters",self); }

    /**
     * visits an explicit constructor invocation
     */
    public void visitExplicitConstructorInvocation(JExplicitConstructorInvocation self) { imp("visitExplicitConstructorInvocation",self); }

    /**
     * visits an array initializer expression
     */
    public void visitArrayInitializer( JArrayInitializer self ) { imp("visitArrayInitializer",self); }

    /**
     * visits an array dimension and initialization expression
     */
    public void visitArrayDimsAndInit( JArrayDimsAndInits self ) { imp("visitArrayDimsAndInit",self); }

    /**
     * visits a warn expression
     */
    public void visitWarnExpression( MJWarnExpression self ) { imp("visitWarnExpression",self); }

    /**
     * visits a math mode expression
     */
    public void visitMathModeExpression( MJMathModeExpression self ) { imp("visitMathModeExpression",self); }

}
