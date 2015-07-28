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
 * $Id: JmlVisitor.java,v 1.25 2007/04/09 22:47:43 leavens Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.MjcVisitor;

/**
 * Implementation of Visitor Design Pattern for KJC.
 *
 * Suggested from: Max R. Andersen(max@cs.auc.dk)
 * !CONVERT! use open classes
 */
public interface JmlVisitor extends MjcVisitor {

    void visitJmlAbruptSpecBody(/*@non_null*/ JmlAbruptSpecBody self );
    void visitJmlAbruptSpecCase(/*@non_null*/ JmlAbruptSpecCase self );
    void visitJmlAccessibleClause(/*@non_null*/ JmlAccessibleClause self );
    void visitJmlAssertStatement(/*@non_null*/ JmlAssertStatement self );
    void visitJmlAssignableClause(/*@non_null*/ JmlAssignableClause self );
    void visitJmlAssumeStatement(/*@non_null*/ JmlAssumeStatement self );
    void visitJmlAxiom(/*@non_null*/ JmlAxiom self );
    void visitJmlBehaviorSpec(/*@non_null*/ JmlBehaviorSpec self );
    void visitJmlBreaksClause(/*@non_null*/ JmlBreaksClause self );
    void visitJmlCallableClause(/*@non_null*/ JmlCallableClause self );
    void visitJmlCapturesClause(/*@non_null*/ JmlCapturesClause self );
    void visitJmlClassBlock(/*@non_null*/ JmlClassBlock self );
    void visitJmlClassDeclaration(/*@non_null*/ JmlClassDeclaration self );
    void visitJmlClassOrGFImport(/*@non_null*/ JmlClassOrGFImport self );
    void visitJmlCodeContract(/*@non_null*/ JmlCodeContract self );
    void visitJmlCompilationUnit(/*@non_null*/ JmlCompilationUnit self );
    void visitJmlConstraint(/*@non_null*/ JmlConstraint self );
    void visitJmlConstructorDeclaration(/*@non_null*/ JmlConstructorDeclaration self );
    void visitJmlConstructorName(/*@non_null*/ JmlConstructorName self );
    void visitJmlContinuesClause(/*@non_null*/ JmlContinuesClause self );
    void visitJmlDebugStatement(/*@non_null*/ JmlDebugStatement self );
    void visitJmlDeclaration(/*@non_null*/ JmlDeclaration self );
    void visitJmlDivergesClause(/*@non_null*/ JmlDivergesClause self );
    void visitJmlDurationClause(/*@non_null*/ JmlDurationClause self );
    void visitJmlDurationExpression(/*@non_null*/ JmlDurationExpression self );
    void visitJmlElemTypeExpression(/*@non_null*/ JmlElemTypeExpression self );
    void visitJmlEnsuresClause(/*@non_null*/ JmlEnsuresClause self );
    void visitJmlExample(/*@non_null*/ JmlExample self );
    void visitJmlExceptionalBehaviorSpec(/*@non_null*/ JmlExceptionalBehaviorSpec self );
    void visitJmlExceptionalExample(/*@non_null*/ JmlExceptionalExample self );
    void visitJmlExceptionalSpecBody(/*@non_null*/ JmlExceptionalSpecBody self );
    void visitJmlExceptionalSpecCase(/*@non_null*/ JmlExceptionalSpecCase self );
    void visitJmlExpression(/*@non_null*/ JmlExpression self );
    void visitJmlExtendingSpecification(/*@non_null*/ JmlExtendingSpecification self );
    void visitJmlFieldDeclaration(/*@non_null*/ JmlFieldDeclaration self );
    void visitJmlForAllVarDecl(/*@non_null*/ JmlForAllVarDecl self );
    void visitJmlFormalParameter(/*@non_null*/ JmlFormalParameter self );
    void visitJmlFreshExpression(/*@non_null*/ JmlFreshExpression self );
    void visitJmlGeneralSpecCase(/*@non_null*/ JmlGeneralSpecCase self );
    void visitJmlGenericSpecBody(/*@non_null*/ JmlGenericSpecBody self );
    void visitJmlGenericSpecCase(/*@non_null*/ JmlGenericSpecCase self );
    void visitJmlGuardedStatement(/*@non_null*/ JmlGuardedStatement self );
    void visitJmlHenceByStatement(/*@non_null*/ JmlHenceByStatement self );
    void visitJmlInGroupClause(/*@non_null*/ JmlInGroupClause self );
    void visitJmlInformalExpression(/*@non_null*/ JmlInformalExpression self );
    void visitJmlInformalStoreRef(/*@non_null*/ JmlInformalStoreRef self );
    void visitJmlInitiallyVarAssertion(/*@non_null*/ JmlInitiallyVarAssertion self );
    void visitJmlInterfaceDeclaration(/*@non_null*/ JmlInterfaceDeclaration self );
    void visitJmlInvariant(/*@non_null*/ JmlInvariant self );
    void visitJmlInvariantForExpression(/*@non_null*/ JmlInvariantForExpression self );
    void visitJmlInvariantStatement(/*@non_null*/ JmlInvariantStatement self );
    void visitJmlIsInitializedExpression(/*@non_null*/ JmlIsInitializedExpression self );
    void visitJmlLabelExpression(/*@non_null*/ JmlLabelExpression self );
    void visitJmlLetVarDecl(/*@non_null*/ JmlLetVarDecl self );
    void visitJmlLockSetExpression(/*@non_null*/ JmlLockSetExpression self );
    void visitJmlLoopInvariant(/*@non_null*/ JmlLoopInvariant self );
    void visitJmlLoopStatement(/*@non_null*/ JmlLoopStatement self );
    void visitJmlMapsIntoClause(/*@non_null*/ JmlMapsIntoClause self );
    void visitJmlMaxExpression(/*@non_null*/ JmlMaxExpression self );
    void visitJmlMeasuredClause(/*@non_null*/ JmlMeasuredClause self );
    void visitJmlMethodDeclaration(/*@non_null*/ JmlMethodDeclaration self );
    void visitJmlMethodName(/*@non_null*/ JmlMethodName self );
    void visitJmlMethodNameList(/*@non_null*/ JmlMethodNameList self );
    void visitJmlMethodSpecification(/*@non_null*/ JmlMethodSpecification self );
    void visitJmlModelProgram(/*@non_null*/ JmlModelProgram self );
    void visitJmlMonitorsForVarAssertion(/*@non_null*/ JmlMonitorsForVarAssertion self );
    void visitJmlName(/*@non_null*/ JmlName self );
    void visitJmlNode(/*@non_null*/ JmlNode self );
    void visitJmlNonNullElementsExpression(/*@non_null*/ 
        JmlNonNullElementsExpression self );
    void visitJmlAssignmentStatement(/*@non_null*/  JmlAssignmentStatement self );
    void visitJmlNondetChoiceStatement(/*@non_null*/ JmlNondetChoiceStatement self );
    void visitJmlNondetIfStatement(/*@non_null*/ JmlNondetIfStatement self );
    void visitJmlNormalBehaviorSpec(/*@non_null*/ JmlNormalBehaviorSpec self );
    void visitJmlNormalExample(/*@non_null*/ JmlNormalExample self );
    void visitJmlNormalSpecBody(/*@non_null*/ JmlNormalSpecBody self );
    void visitJmlNormalSpecCase(/*@non_null*/ JmlNormalSpecCase self );
    void visitJmlNotAssignedExpression(/*@non_null*/ JmlNotAssignedExpression self );
    void visitJmlNotModifiedExpression(/*@non_null*/ JmlNotModifiedExpression self );
    void visitJmlOnlyAccessedExpression(/*@non_null*/ JmlOnlyAccessedExpression self );
    void visitJmlOnlyAssignedExpression(/*@non_null*/ JmlOnlyAssignedExpression self );
    void visitJmlOnlyCalledExpression(/*@non_null*/ JmlOnlyCalledExpression self );
    void visitJmlOnlyCapturedExpression(/*@non_null*/ JmlOnlyCapturedExpression self );
    void visitJmlOldExpression(/*@non_null*/ JmlOldExpression self );
    void visitJmlPackageImport(/*@non_null*/ JmlPackageImport self );
    void visitJmlPredicate(/*@non_null*/ JmlPredicate self );
    void visitJmlPredicateKeyword(/*@non_null*/ JmlPredicateKeyword self);
    void visitJmlPreExpression(/*@non_null*/ JmlPreExpression self );
    void visitJmlReachExpression(/*@non_null*/ JmlReachExpression self );
    void visitJmlReadableIfVarAssertion(/*@non_null*/ JmlReadableIfVarAssertion self );
    void visitJmlWritableIfVarAssertion(/*@non_null*/ JmlWritableIfVarAssertion self );
    void visitJmlRedundantSpec(/*@non_null*/ JmlRedundantSpec self );
    void visitJmlRefinePrefix(/*@non_null*/ JmlRefinePrefix self );
    void visitJmlRelationalExpression(/*@non_null*/ JmlRelationalExpression self );
    void visitJmlRepresentsDecl(/*@non_null*/ JmlRepresentsDecl self );
    void visitJmlRequiresClause(/*@non_null*/ JmlRequiresClause self );
    void visitJmlResultExpression(/*@non_null*/ JmlResultExpression self );
    void visitJmlReturnsClause(/*@non_null*/ JmlReturnsClause self );
    void visitJmlSetComprehension(/*@non_null*/ JmlSetComprehension self );
    void visitJmlSetStatement(/*@non_null*/ JmlSetStatement self );
    void visitJmlRefiningStatement(/*@non_null*/ JmlRefiningStatement self );
    void visitJmlSignalsOnlyClause(/*@non_null*/ JmlSignalsOnlyClause self );
    void visitJmlSignalsClause(/*@non_null*/ JmlSignalsClause self );
    void visitJmlSpaceExpression(/*@non_null*/ JmlSpaceExpression self );
    void visitJmlSpecBody(/*@non_null*/ JmlSpecBody self );
    void visitJmlSpecExpression(/*@non_null*/ JmlSpecExpression self );
    void visitJmlSpecQuantifiedExpression(/*@non_null*/ JmlSpecQuantifiedExpression self );
    void visitJmlSpecStatement(/*@non_null*/ JmlSpecStatement self );
    void visitJmlSpecification(/*@non_null*/ JmlSpecification self );
    void visitJmlSpecVarDecl(/*@non_null*/ JmlSpecVarDecl self );
    void visitJmlStoreRef(/*@non_null*/ JmlStoreRef self );
    void visitJmlStoreRefExpression(/*@non_null*/ JmlStoreRefExpression self );
    void visitJmlStoreRefKeyword(/*@non_null*/ JmlStoreRefKeyword self );
    void visitJmlTypeExpression(/*@non_null*/ JmlTypeExpression self );
    void visitJmlTypeOfExpression(/*@non_null*/ JmlTypeOfExpression self );
    void visitJmlUnreachableStatement(/*@non_null*/ JmlUnreachableStatement self );
    void visitJmlVariantFunction(/*@non_null*/ JmlVariantFunction self );
    void visitJmlVariableDefinition(/*@non_null*/ JmlVariableDefinition self );
    void visitJmlWhenClause(/*@non_null*/ JmlWhenClause self );
    void visitJmlWorkingSpaceClause(/*@non_null*/ JmlWorkingSpaceClause self );
    void visitJmlWorkingSpaceExpression(/*@non_null*/ JmlWorkingSpaceExpression self );
}
