/*
 * Copyright (C) 2001-2002 Iowa State University
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
 * $Id: JmlAbstractVisitor.java,v 1.30 2007/04/09 22:47:42 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.JAddExpression;
import org.multijava.mjc.JArrayAccessExpression;
import org.multijava.mjc.JArrayDimsAndInits;
import org.multijava.mjc.JArrayInitializer;
import org.multijava.mjc.JArrayLengthExpression;
import org.multijava.mjc.JAssertStatement;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JBinaryExpression;
import org.multijava.mjc.JBitwiseExpression;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JBreakStatement;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JCatchClause;
import org.multijava.mjc.JCharLiteral;
import org.multijava.mjc.JClassBlock;
import org.multijava.mjc.JClassDeclaration;
import org.multijava.mjc.JClassExpression;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JClassOrGFImport;
import org.multijava.mjc.JCompilationUnit;
import org.multijava.mjc.JCompoundAssignmentExpression;
import org.multijava.mjc.JCompoundStatement;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JConditionalExpression;
import org.multijava.mjc.JConditionalOrExpression;
import org.multijava.mjc.JConstructorBlock;
import org.multijava.mjc.JConstructorDeclaration;
import org.multijava.mjc.JContinueStatement;
import org.multijava.mjc.JDivideExpression;
import org.multijava.mjc.JDoStatement;
import org.multijava.mjc.JEmptyStatement;
import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExplicitConstructorInvocation;
import org.multijava.mjc.JExpressionListStatement;
import org.multijava.mjc.JExpressionStatement;
import org.multijava.mjc.JFieldDeclaration;
import org.multijava.mjc.JForStatement;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JIfStatement;
import org.multijava.mjc.JInitializerDeclaration;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JInterfaceDeclaration;
import org.multijava.mjc.JLabeledStatement;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JMinusExpression;
import org.multijava.mjc.JModuloExpression;
import org.multijava.mjc.JMultExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNewAnonymousClassExpression;
import org.multijava.mjc.JNewArrayExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.mjc.JPackageImport;
import org.multijava.mjc.JPackageName;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JPostfixExpression;
import org.multijava.mjc.JPrefixExpression;
import org.multijava.mjc.JRealLiteral;
import org.multijava.mjc.JRelationalExpression;
import org.multijava.mjc.JReturnStatement;
import org.multijava.mjc.JShiftExpression;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JStringLiteral;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JSwitchGroup;
import org.multijava.mjc.JSwitchLabel;
import org.multijava.mjc.JSwitchStatement;
import org.multijava.mjc.JSynchronizedStatement;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JThrowStatement;
import org.multijava.mjc.JTryCatchStatement;
import org.multijava.mjc.JTryFinallyStatement;
import org.multijava.mjc.JTypeDeclarationStatement;
import org.multijava.mjc.JTypeNameExpression;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.mjc.JUnaryPromote;
import org.multijava.mjc.JVariableDeclarationStatement;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.JWhileStatement;
import org.multijava.mjc.MJGenericFunctionDecl;
import org.multijava.mjc.MJMathModeExpression;
import org.multijava.mjc.MJTopLevelMethodDeclaration;
import org.multijava.mjc.MJWarnExpression;

/**
 * An abstract JML visitor class to facilitate writing concrete
 * visitor classes that implements the interface JmlVisitor. Each 
 * visitor method defined in this class performs no action; concrete
 * subclasses should override them appropriately.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.30 $
 */
public abstract class JmlAbstractVisitor extends org.multijava.util.Utils 
    implements org.jmlspecs.checker.Constants, JmlVisitor {

    // ----------------------------------------------------------------------
    // JML-SPECIFIC VISITORS
    // ----------------------------------------------------------------------

    public void visitJmlAbruptSpecBody(/*@non_null*/ JmlAbruptSpecBody self ) {}
    public void visitJmlAbruptSpecCase(/*@non_null*/ JmlAbruptSpecCase self ) {}
    public void visitJmlAccessibleClause(/*@non_null*/ JmlAccessibleClause self ) {}
    public void visitJmlAssertStatement(/*@non_null*/ JmlAssertStatement self ) {}
    public void visitJmlAssignableClause(/*@non_null*/ JmlAssignableClause self ) {}
    public void visitJmlAssumeStatement(/*@non_null*/ JmlAssumeStatement self ) {}
    public void visitJmlAxiom(/*@non_null*/ JmlAxiom self ) {}
    public void visitJmlBehaviorSpec(/*@non_null*/ JmlBehaviorSpec self ) {}
    public void visitJmlBreaksClause(/*@non_null*/ JmlBreaksClause self ) {}
    public void visitJmlCallableClause(/*@non_null*/ JmlCallableClause self ) {}
    public void visitJmlCapturesClause(/*@non_null*/ JmlCapturesClause self ) {}
    public void visitJmlClassBlock(/*@non_null*/ JmlClassBlock self ) {}
    public void visitJmlClassDeclaration(/*@non_null*/ JmlClassDeclaration self ) {}
    public void visitJmlClassOrGFImport(/*@non_null*/ JmlClassOrGFImport self ) {}
    public void visitJmlCompilationUnit(/*@non_null*/ JmlCompilationUnit self ) {}
    public void visitJmlCodeContract(/*@non_null*/ JmlCodeContract self ) {}
    public void visitJmlConstraint(/*@non_null*/ JmlConstraint self ) {}
    public void visitJmlConstructorDeclaration(/*@non_null*/ 
       JmlConstructorDeclaration self ) {}
    public void visitJmlConstructorName(/*@non_null*/ JmlConstructorName self ) {}
    public void visitJmlContinuesClause(/*@non_null*/ JmlContinuesClause self ) {}
    public void visitJmlDebugStatement(/*@non_null*/ JmlDebugStatement self ) {}
    public void visitJmlDivergesClause(/*@non_null*/ JmlDivergesClause self ) {}
    public void visitJmlDurationClause(/*@non_null*/ JmlDurationClause self ) {}
    public void visitJmlDurationExpression(/*@non_null*/ JmlDurationExpression self ) {}
    public void visitJmlElemTypeExpression(/*@non_null*/ JmlElemTypeExpression self ) {}
    public void visitJmlEnsuresClause(/*@non_null*/ JmlEnsuresClause self ) {}
    public void visitJmlExample(/*@non_null*/ JmlExample self ) {}
    public void visitJmlExceptionalBehaviorSpec(/*@non_null*/ 
       JmlExceptionalBehaviorSpec self ) {}
    public void visitJmlExceptionalExample(/*@non_null*/ JmlExceptionalExample self ) {}
    public void visitJmlExceptionalSpecBody(/*@non_null*/ JmlExceptionalSpecBody self ) {}
    public void visitJmlExceptionalSpecCase(/*@non_null*/ JmlExceptionalSpecCase self ) {}
    public void visitJmlExtendingSpecification(/*@non_null*/ 
       JmlExtendingSpecification self ) {}
    public void visitJmlFieldDeclaration(/*@non_null*/ JmlFieldDeclaration self ) {}
    public void visitJmlForAllVarDecl(/*@non_null*/ JmlForAllVarDecl self ) {}
    public void visitJmlFormalParameter(/*@non_null*/ JmlFormalParameter self ) {}
    public void visitJmlFreshExpression(/*@non_null*/ JmlFreshExpression self ) {}
    public void visitJmlGenericSpecBody(/*@non_null*/ JmlGenericSpecBody self ) {}
    public void visitJmlGenericSpecCase(/*@non_null*/ JmlGenericSpecCase self ) {}
    public void visitJmlGuardedStatement(/*@non_null*/ JmlGuardedStatement self ) {}
    public void visitJmlHenceByStatement(/*@non_null*/ JmlHenceByStatement self ) {}
    public void visitJmlInGroupClause(/*@non_null*/ JmlInGroupClause self ) {}
    public void visitJmlInformalExpression(/*@non_null*/ JmlInformalExpression self ) {}
    public void visitJmlInformalStoreRef(/*@non_null*/ JmlInformalStoreRef self ) {}
    public void visitJmlInitiallyVarAssertion(/*@non_null*/ 
       JmlInitiallyVarAssertion self ) {}
    public void visitJmlInterfaceDeclaration(/*@non_null*/ JmlInterfaceDeclaration self ) {}
    public void visitJmlInvariant(/*@non_null*/ JmlInvariant self ) {}
    public void visitJmlInvariantForExpression(/*@non_null*/ 
       JmlInvariantForExpression self ) {}
    public void visitJmlInvariantStatement(/*@non_null*/ JmlInvariantStatement self ) {}
    public void visitJmlIsInitializedExpression(/*@non_null*/ 
       JmlIsInitializedExpression self ) {}
    public void visitJmlLabelExpression(/*@non_null*/ JmlLabelExpression self ) {}
    public void visitJmlLetVarDecl(/*@non_null*/ JmlLetVarDecl self ) {}
    public void visitJmlLockSetExpression(/*@non_null*/ JmlLockSetExpression self ) {}
    public void visitJmlLoopInvariant(/*@non_null*/ JmlLoopInvariant self ) {}
    public void visitJmlLoopStatement(/*@non_null*/ JmlLoopStatement self ) {}
    public void visitJmlMapsIntoClause(/*@non_null*/ JmlMapsIntoClause self ) {}
    public void visitJmlMaxExpression(/*@non_null*/ JmlMaxExpression self ) {}
    public void visitJmlMeasuredClause(/*@non_null*/ JmlMeasuredClause self ) {}
    public void visitJmlMethodDeclaration(/*@non_null*/ JmlMethodDeclaration self ) {}
    public void visitJmlMethodName(/*@non_null*/ JmlMethodName self ) {}
    public void visitJmlMethodNameList(/*@non_null*/ JmlMethodNameList self ) {}
    public void visitJmlModelProgram(/*@non_null*/ JmlModelProgram self ) {}
    public void visitJmlMonitorsForVarAssertion(/*@non_null*/ 
       JmlMonitorsForVarAssertion self ) {}
    public void visitJmlName(/*@non_null*/ JmlName self ) {}
    public void visitJmlNonNullElementsExpression(/*@non_null*/ 
         JmlNonNullElementsExpression self ) {}
    public void visitJmlAssignmentStatement(/*@non_null*/  
       JmlAssignmentStatement self ) { }
    public void visitJmlNondetChoiceStatement(/*@non_null*/ 
       JmlNondetChoiceStatement self ) {}
    public void visitJmlNondetIfStatement(/*@non_null*/ JmlNondetIfStatement self ) {}
    public void visitJmlNormalBehaviorSpec(/*@non_null*/ JmlNormalBehaviorSpec self ) {}
    public void visitJmlNormalExample(/*@non_null*/ JmlNormalExample self ) {}
    public void visitJmlNormalSpecBody(/*@non_null*/ JmlNormalSpecBody self ) {}
    public void visitJmlNormalSpecCase(/*@non_null*/ JmlNormalSpecCase self ) {}
    public void visitJmlNotAssignedExpression(/*@non_null*/ 
       JmlNotAssignedExpression self ) {}
    public void visitJmlNotModifiedExpression(/*@non_null*/ 
       JmlNotModifiedExpression self ) {}
    public void visitJmlOnlyAccessedExpression(/*@non_null*/ 
       JmlOnlyAccessedExpression self ) {}
    public void visitJmlOnlyAssignedExpression(/*@non_null*/ 
       JmlOnlyAssignedExpression self ) {}
    public void visitJmlOnlyCalledExpression(/*@non_null*/ 
       JmlOnlyCalledExpression self ) {}
    public void visitJmlOnlyCapturedExpression(/*@non_null*/ 
       JmlOnlyCapturedExpression self ) {}
    public void visitJmlOldExpression(/*@non_null*/ JmlOldExpression self ) {}
    public void visitJmlPackageImport(/*@non_null*/ JmlPackageImport self ) {}
    public void visitJmlPredicate(/*@non_null*/ JmlPredicate self) { }
    public void visitJmlPredicateKeyword(/*@non_null*/ JmlPredicateKeyword self) { }
    public void visitJmlPreExpression(/*@non_null*/ JmlPreExpression self ) {}
    public void visitJmlReachExpression(/*@non_null*/ JmlReachExpression self ) {}
    public void visitJmlReadableIfVarAssertion(/*@non_null*/ 
       JmlReadableIfVarAssertion self ) {}
    public void visitJmlWritableIfVarAssertion(/*@non_null*/ 
       JmlWritableIfVarAssertion self ) {}
    public void visitJmlRedundantSpec(/*@non_null*/ JmlRedundantSpec self ) {}
    public void visitJmlRefinePrefix(/*@non_null*/ JmlRefinePrefix self ) {}
    public void visitJmlRelationalExpression(/*@non_null*/ JmlRelationalExpression self ) {}
    public void visitJmlRepresentsDecl(/*@non_null*/ JmlRepresentsDecl self ) {}
    public void visitJmlRequiresClause(/*@non_null*/ JmlRequiresClause self ) {}
    public void visitJmlResultExpression(/*@non_null*/ JmlResultExpression self ) {}
    public void visitJmlReturnsClause(/*@non_null*/ JmlReturnsClause self ) {}
    public void visitJmlSetComprehension(/*@non_null*/ JmlSetComprehension self ) {}
    public void visitJmlSetStatement(/*@non_null*/ JmlSetStatement self ) {}
    public void visitJmlRefiningStatement(/*@non_null*/ JmlRefiningStatement self ) {}
    public void visitJmlSignalsOnlyClause(/*@non_null*/ JmlSignalsOnlyClause self ) {}
    public void visitJmlSignalsClause(/*@non_null*/ JmlSignalsClause self ) {}
    public void visitJmlSpaceExpression(/*@non_null*/ JmlSpaceExpression self ) {}
    public void visitJmlSpecExpression(/*@non_null*/ JmlSpecExpression self ) {}
    public void visitJmlSpecQuantifiedExpression(/*@non_null*/ 
       JmlSpecQuantifiedExpression self ) {}
    public void visitJmlSpecStatement(/*@non_null*/ JmlSpecStatement self ) {}
    public void visitJmlSpecification(/*@non_null*/ JmlSpecification self ) {}
    public void visitJmlStoreRefExpression(/*@non_null*/ JmlStoreRefExpression self ) {}
    public void visitJmlStoreRefKeyword(/*@non_null*/ JmlStoreRefKeyword self ) {}
    public void visitJmlTypeExpression(/*@non_null*/ JmlTypeExpression self ) {}
    public void visitJmlTypeOfExpression(/*@non_null*/ JmlTypeOfExpression self ) {}
    public void visitJmlUnreachableStatement(/*@non_null*/ JmlUnreachableStatement self ) {}
    public void visitJmlVariantFunction(/*@non_null*/ JmlVariantFunction self ) {}
    public void visitJmlVariableDefinition(/*@non_null*/ JmlVariableDefinition self ) {}
    public void visitJmlWhenClause(/*@non_null*/ JmlWhenClause self ) {}
    public void visitJmlWorkingSpaceClause(/*@non_null*/ JmlWorkingSpaceClause self ) {}
    public void visitJmlWorkingSpaceExpression(/*@non_null*/ JmlWorkingSpaceExpression self ) {}

    // ----------------------------------------------------------------------
    // NOT NEEDED, BUT DEFINED IN JmlVisitor, PERHAPS, SHOULD BE CLEANED OUT!
    // ----------------------------------------------------------------------
    public void visitJmlDeclaration(/*@non_null*/ JmlDeclaration self ) {}
    public void visitJmlExpression(/*@non_null*/ JmlExpression self ) {}
    public void visitJmlGeneralSpecCase(/*@non_null*/ JmlGeneralSpecCase self ) {}
    public void visitJmlMethodSpecification(/*@non_null*/ JmlMethodSpecification self ) {}
    public void visitJmlNode(/*@non_null*/ JmlNode self ) {}
    public void visitJmlSpecBody(/*@non_null*/ JmlSpecBody self ) {}
    public void visitJmlSpecVarDecl(/*@non_null*/ JmlSpecVarDecl self ) {}
    public void visitJmlStoreRef(/*@non_null*/ JmlStoreRef self ) {}

    // ----------------------------------------------------------------------
    // MJC VISITORS
    // ----------------------------------------------------------------------

    /** Visits the given compilation unit. */
    public void visitCompilationUnit(/*@non_null*/ JCompilationUnit self ) {}

    /** Visits the given class declaration. */
    public void visitClassDeclaration(/*@non_null*/ JClassDeclaration self ) {}

    /** Visits the given interface declaration. */
    public void visitInterfaceDeclaration(/*@non_null*/ JInterfaceDeclaration self ) {}

    /** Visits the given generic function declaration. */
    public void visitGenericFunctionDecl(/*@non_null*/ MJGenericFunctionDecl self ) {}
    
    /** Visits the given field declaration. */
    public void visitFieldDeclaration(/*@non_null*/ JFieldDeclaration self ) {}

    /** Visits the given method declaration. */
    public void visitMethodDeclaration(/*@non_null*/ JMethodDeclaration self ) {}

    /** Visits the given initializer declaration. */
    public void visitInitializerDeclaration(/*@non_null*/ JInitializerDeclaration self ) {
    }

    /** Visits the given external method declaration. */
    public void visitTopLevelMethodDeclaration(/*@non_null*/ MJTopLevelMethodDeclaration self ) {}

    /** Visits the given constructor declaration. */
    public void visitConstructorDeclaration(/*@non_null*/ JConstructorDeclaration self ) {
    }

    // ----------------------------------------------------------------------
    // STATEMENT
    // ----------------------------------------------------------------------

    /** Visits the given while statement. */
    public void visitWhileStatement(/*@non_null*/ JWhileStatement self ) {}

    /** Visits the given variable declaration statement. */
    public void visitVariableDeclarationStatement(/*@non_null*/ JVariableDeclarationStatement self) {}

    /** Visits the given variable declaration statement. */
    public void visitVariableDefinition(/*@non_null*/ JVariableDefinition self ) {}

    /** Visits the given try-catch statement. */
    public void visitTryCatchStatement(/*@non_null*/ JTryCatchStatement self ) {}
    /** Visits the given try-finally statement. */
    public void visitTryFinallyStatement(/*@non_null*/ JTryFinallyStatement self ) {}

    /** Visits the given throw statement. */
    public void visitThrowStatement(/*@non_null*/ JThrowStatement self ) {}

    /** Visits the given synchronized statement. */
    public void visitSynchronizedStatement(/*@non_null*/ JSynchronizedStatement self ) {}

    /** Visits the given switch statement. */
    public void visitSwitchStatement(/*@non_null*/ JSwitchStatement self ) {}

    /** Visits the given assert statement. */
    public void visitAssertStatement(/*@non_null*/ JAssertStatement self ) {}

    /** Visits the given return statement. */
    public void visitReturnStatement(/*@non_null*/ JReturnStatement self ) {}

    /** Visits the given labeled statement. */
    public void visitLabeledStatement(/*@non_null*/ JLabeledStatement self ) {}

    /** Visits the given if statement. */
    public void visitIfStatement(/*@non_null*/ JIfStatement self ) {}

    /** Visits the given for statement. */
    public void visitForStatement(/*@non_null*/ JForStatement self ) {}

    /** Visits the given compound statement. */
    public void visitCompoundStatement(/*@non_null*/ JCompoundStatement self ) {}

    /** Visits the given compound statement. */
    public void visitCompoundStatement(/*@non_null*/JStatement[] body) {}

    /** Visits the given expression statement. */
    public void visitExpressionStatement(/*@non_null*/ JExpressionStatement self ) {}

    /** Visits the given expression list statement. */
    public void visitExpressionListStatement(/*@non_null*/ JExpressionListStatement self ) {}

    /** Visits the given empty statement. */
    public void visitEmptyStatement(/*@non_null*/ JEmptyStatement self ) {}

    /** Visits the given do statement. */
    public void visitDoStatement(/*@non_null*/ JDoStatement self ) {}

    /** Visits the given continue statement. */
    public void visitContinueStatement(/*@non_null*/ JContinueStatement self ) {}

    /** Visits the given break statement. */
    public void visitBreakStatement(/*@non_null*/ JBreakStatement self ) {}

    /** Visits the given block statement. */
    public void visitBlockStatement(/*@non_null*/ JBlock self ) {}

    /** Visits the given constructor block. */
    public void visitConstructorBlock(/*@non_null*/ JConstructorBlock self ) {}

    /** Visits the given class block. */
    public void visitClassBlock(/*@non_null*/ JClassBlock self ) {}

    /** Visits the given type declaration statement. */
    public void visitTypeDeclarationStatement(/*@non_null*/JTypeDeclarationStatement self) {}

    // ----------------------------------------------------------------------
    // EXPRESSION
    // ----------------------------------------------------------------------

    /** Visits the given unary expression. */
    public void visitUnaryExpression(/*@non_null*/ JUnaryExpression self ) {}

    /** Visits the given type name expression. */
    public void visitTypeNameExpression(/*@non_null*/ JTypeNameExpression self ) {}

    /** Visits the given this expression. */
    public void visitThisExpression(/*@non_null*/ JThisExpression self ) {}

    /** Visits the given super expression. */
    public void visitSuperExpression(/*@non_null*/ JSuperExpression self ) {}

    /** Visits the given shift expression. */
    public void visitShiftExpression(/*@non_null*/ JShiftExpression self ) {}

    /** Visits the given relational expression. */
    public void visitRelationalExpression(/*@non_null*/ JRelationalExpression self ) {}

    /** Visits the given prefix expression. */
    public void visitPrefixExpression(/*@non_null*/ JPrefixExpression self ) {}

    /** Visits the given postfix expression. */
    public void visitPostfixExpression(/*@non_null*/ JPostfixExpression self ) {}

    /** Visits the given parenthesed expression. */
    public void visitParenthesedExpression(/*@non_null*/ JParenthesedExpression self ) {}

    /** Visits the given object allocator expression. */
    public void visitNewObjectExpression(/*@non_null*/ JNewObjectExpression self ) {}

    /** Visits the given object allocator expression for an anonymous class. */
    public void visitNewAnonymousClassExpression(/*@non_null*/ JNewAnonymousClassExpression self ) {}

    /** Visits the given array allocator expression. */
    public void visitNewArrayExpression(/*@non_null*/ JNewArrayExpression self ) {}

    /** Visits the given name expression. */
    public void visitNameExpression(/*@non_null*/ JNameExpression self ) {}

    /** Visits the given binary expression with the given operator. */
    protected void visitBinaryExpression(/*@non_null*/ JBinaryExpression self, 
                                          String oper ) {}

    /** Visits the given add expression. */
    public void visitAddExpression(/*@non_null*/ JAddExpression self ) {}

    /** Visits the given boolean AND expression. */
    public void visitConditionalAndExpression(/*@non_null*/ JConditionalAndExpression self ) {}

    /** Visits the given boolean OR expression. */
    public void visitConditionalOrExpression(/*@non_null*/ JConditionalOrExpression self ) {}

    /** Visits the given divide expression. */
    public void visitDivideExpression(/*@non_null*/ JDivideExpression self ) {}

    /** Visits the given minus expression. */
    public void visitMinusExpression(/*@non_null*/ JMinusExpression self ) {}

    /** Visits the given modulo division expression. */
    public void visitModuloExpression(/*@non_null*/ JModuloExpression self ) {}

    /** Visits the given multiplication expression. */
    public void visitMultExpression(/*@non_null*/ JMultExpression self ) {}

    /** Visits the given method call expression. */
    public void visitMethodCallExpression(/*@non_null*/ JMethodCallExpression self ) {}

    /** Visits the given local variable expression. */
    public void visitLocalVariableExpression(/*@non_null*/ JLocalVariableExpression self ) {}

    /** Visits the given instanceof expression. */
    public void visitInstanceofExpression(/*@non_null*/ JInstanceofExpression self ) {}

    /** Visits the given equality expression. */
    public void visitEqualityExpression(/*@non_null*/ JEqualityExpression self ) {}

    /** Visits the given conditional expression. */
    public void visitConditionalExpression(/*@non_null*/ JConditionalExpression self ) {}

    /** Visits the given compound expression. */
    public void visitCompoundAssignmentExpression(/*@non_null*/ JCompoundAssignmentExpression self) {}

    /** Visits the given field expression. */
    public void visitFieldExpression(/*@non_null*/ JClassFieldExpression self ) {}

    /** Visits the given class expression. */
    public void visitClassExpression(/*@non_null*/ JClassExpression self ) {}

    /** Visits the given cast expression. */
    public void visitCastExpression(/*@non_null*/ JCastExpression self ) {}

    /** Visits the given unary promotion expression. */
    public void visitUnaryPromoteExpression(/*@non_null*/ JUnaryPromote self ) {}

    /** Visits the given bitwise expression. */
    public void visitBitwiseExpression(/*@non_null*/ JBitwiseExpression self ) {}

    /** Visits the given assignment expression. */
    public void visitAssignmentExpression(/*@non_null*/ JAssignmentExpression self ) {}

    /** Visits the given array length expression. */
    public void visitArrayLengthExpression(/*@non_null*/ JArrayLengthExpression self ) {}

    /** Visits the given array access expression. */
    public void visitArrayAccessExpression(/*@non_null*/ JArrayAccessExpression self ) {}

    /** Visits the given warn expression. */
    public void visitWarnExpression(/*@non_null*/ MJWarnExpression self ) {}
    
    /** Visits the given math mode expression. */
    public void visitMathModeExpression(/*@non_null*/ MJMathModeExpression self ) {}

    // ----------------------------------------------------------------------
    // UTILS
    // ----------------------------------------------------------------------

    /* Visits the given switch label. */
    public void visitSwitchLabel(/*@non_null*/ JSwitchLabel self ) {}

    /** Visits the given switch group. */
    public void visitSwitchGroup(/*@non_null*/ JSwitchGroup self ) {}

    /** Visits the given catch clause. */
    public void visitCatchClause(/*@non_null*/ JCatchClause self ) {}

    /** Visits the given boolean literal. */
    public void visitBooleanLiteral(/*@non_null*/ JBooleanLiteral self ) {}

    /** Visits the given character literal. */
    public void visitCharLiteral(/*@non_null*/ JCharLiteral self ) {}

    /** Visits the given ordinal literal. */
    public void visitOrdinalLiteral(/*@non_null*/ JOrdinalLiteral self ) {}

    /** Visits the given byte literal. */
    protected void visitByteLiteral(byte value ) {}

    /** Visits the given int literal. */
    protected void visitIntLiteral(int value) {}

    /** Visits the given long literal. */
    protected void visitLongLiteral(long value) {}

    /** Visits the given short literal. */
    protected void visitShortLiteral(short value) {}

    /** Visits the given real literal. */
    public void visitRealLiteral(/*@non_null*/ JRealLiteral self ) {}

    /** Visits the given double literal. */
    protected void visitDoubleLiteral(double value) {}

    /** Visits the given float literal. */
    protected void visitFloatLiteral(float value) {}

    /** Visits the given string literal. */
    public void visitStringLiteral(/*@non_null*/ JStringLiteral self) {}

    /** Visits the given null literal. */
    public void visitNullLiteral(/*@non_null*/ JNullLiteral self ) {}

    /** Visits the given package name statement. */
    public void visitPackageName(/*@non_null*/ JPackageName self ) {}

    /** Visits the given package import statement. */
    public void visitPackageImport(/*@non_null*/ JPackageImport self ) {}

    /** Visits the given class import statement. */
    public void visitClassOrGFImport(/*@non_null*/ JClassOrGFImport self ) {}

    /** Visits the given formal parameters. */
    public void visitFormalParameters(/*@non_null*/ JFormalParameter self ) {}

    /** Visits the given explicit constructor invocation. */
    public void visitExplicitConstructorInvocation(/*@non_null*/ JExplicitConstructorInvocation self) {}

    /** Visits the given array initializer. */
    public void visitArrayInitializer(/*@non_null*/ JArrayInitializer self ) {}

    /** Visits the given array dimension and initialization expression. */
    public void visitArrayDimsAndInit(/*@non_null*/ JArrayDimsAndInits self ) {}
}

