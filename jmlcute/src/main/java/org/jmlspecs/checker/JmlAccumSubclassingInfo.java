package org.jmlspecs.checker;

import java.util.ArrayList;
import java.util.Iterator;

import org.multijava.mjc.CType;
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
import org.multijava.mjc.JClassExpression;
import org.multijava.mjc.JClassFieldExpression;
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
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JExpressionListStatement;
import org.multijava.mjc.JExpressionStatement;
import org.multijava.mjc.JForStatement;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JIfStatement;
import org.multijava.mjc.JInstanceofExpression;
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
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JPhylum;
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
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JTypeNameExpression;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.mjc.JUnaryPromote;
import org.multijava.mjc.JVariableDeclarationStatement;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.JWhileStatement;
import org.multijava.mjc.MJMathModeExpression;
import org.multijava.mjc.MJTopLevelMethodDeclaration;

/**
 * @author not attributable
 * @version $Revision: 1.14 $
 */
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
 * $Id: JmlAccumSubclassingInfo.java,v 1.14 2007/04/18 23:04:37 leavens Exp $
 */

public class JmlAccumSubclassingInfo 
    extends JmlVisitorNI implements Constants 
{

    public JmlAccumSubclassingInfo() {
	assignedFields = new ArrayList();
	accessedFields = new ArrayList();
	calledMethods = new ArrayList();
    }
    public JExpression[] getAssignedFields() {
	return (JExpression[]) assignedFields
	    .toArray(new JExpression[assignedFields.size()]);
    }
    public JExpression[] getAccessedFields() {
	return (JExpression[]) accessedFields
	    .toArray(new JExpression[accessedFields.size()]);
    }
    public JExpression[] getCalledMethods() {
	return (JExpression[]) calledMethods
	    .toArray(new JExpression[calledMethods.size()]);
    }

    public void visitMethodDeclaration( JMethodDeclaration self )
    {
	JBlock body = self.body();
	if (body != null) {
	    body.accept(this);
	}
    } // visitMethodDeclaration

    public void visitConstructorDeclaration(JConstructorDeclaration self) {
	JBlock body = self.body();
	if (body != null) {
	    body.accept(this);
	}
    } // visitConstructorDeclaration

    public void visitBlockStatement( JBlock self ) {
	JStatement[] body = self.body();
	if (body != null) {
	    visitCompoundStatement(body);
	}
    } // visitBlockStatement

    public void visitConstructorBlock(JConstructorBlock self)
    {
	JExpression explicitSuper = self.explicitSuper();
	JStatement blockCall = self.blockCall();
	JStatement[] body = self.body();

	if (explicitSuper != null) {
	    explicitSuper.accept(this);
	}
	if (blockCall != null) {
	    blockCall.accept(this);
	}
	if (body != null) {
	    visitCompoundStatement(body);
	}
    } // visitConstructorBlock

    public void visitCompoundStatement(JStatement[] body)
    {
	for (int i = 0; i < body.length; i++) {
	    body[i].accept(this);
	}
    } // visitCompoundStatement

    public void visitCompoundStatement( JCompoundStatement self )
    {
	JStatement[] body = self.body();
	visitCompoundStatement(body);
    } // visitCompoundStatement

    public void visitVariableDeclarationStatement
	(JVariableDeclarationStatement self)
    {
	JVariableDefinition[] vars = self.getVars();
	for (int i = 0; i < vars.length; i++) {
	    vars[i].accept(this);
	}
    } // visitVariableDeclarationStatement

    public void visitVariableDefinition( JVariableDefinition self )
    {
	CType type = self.getType();
	//    String ident = self.ident();
	JExpression expr = self.expr();
	//    System.out.println(ident);
	if (expr != null) {
	    expr.accept(this);
	}
    } // visitVariableDefinition

    public void visitJmlVariableDefinition( JmlVariableDefinition self ) {
        visitVariableDefinition(self);
    }

    public void visitAssertStatement( JAssertStatement self )
    {
	self.predicate().accept(this);
    } // visitAssertStatement

    public void visitBreakStatement( JBreakStatement self )
    {
	//    System.out.println("visitBreakStatement");
    } // visitBreakStatement

    public void visitContinueStatement( JContinueStatement self )
    {
	//    System.out.println("visitContinueStatement");
    } // visitContinueStatement

    public void visitEmptyStatement( JEmptyStatement self ) { }

    public void visitExpressionListStatement( JExpressionListStatement self )
    {
	JExpression[] exprs = self.exprs();
	for (int i = 0; i < exprs.length; i++) {
	    exprs[i].accept(this);
	}
    } // visitExpressionListStatement

    public void visitExpressionStatement( JExpressionStatement self )
    {
	JExpression expr = self.expr();
	expr.accept(this);
    } // visitExpressionStatement

    public void visitIfStatement( JIfStatement self )
    {
	JExpression cond = self.cond();
	JStatement thenClause = self.thenClause();
	JStatement elseClause = self.elseClause();

	cond.accept(this);
	thenClause.accept(this);
	if (elseClause != null) {
	    elseClause.accept(this);
	}
    } // visitIfStatement

    public void visitDoStatement( JDoStatement self )
    {
	JExpression cond = self.cond();
	JStatement body = self.body();
	body.accept(this);
	cond.accept(this);
    } // visitDoStatement

    public void visitWhileStatement(JWhileStatement self) {
	JExpression cond = self.cond();
	JStatement body = self.body();
	cond.accept(this);
	body.accept(this);
    } // visitWhileStatement


    public void visitForStatement( JForStatement self )
    {
	JStatement init = self.init();
	JExpression cond = self.cond();
	JStatement incr = self.incr();
	JStatement body = self.body();

	if (init != null) {
	    init.accept(this);
	}
	if (cond != null) {
	    cond.accept(this);
	}
	if (incr != null) {
	    incr.accept(this);
	}
	body.accept(this);
    } // visitForStatement

    public void visitSwitchStatement(JSwitchStatement self)
    {
	JExpression expr = self.expr();
	JSwitchGroup[] groups = self.groups();

	expr.accept(this);
	for (int i = 0; i < groups.length; i++) {
	    groups[i].accept(this);
	}
    } // visitSwitchStatement

    public void visitSwitchGroup( JSwitchGroup self )
    {
	JSwitchLabel[] labels = self.labels();
	JStatement[] stmts = self.getStatements();

	for (int i = 0; i < labels.length; i++) {
	    labels[i].accept(this);
	}
	for (int i = 0; i < stmts.length; i++) {
	    stmts[i].accept(this);
	}
    } // visitSwitchGroup

    public void visitSwitchLabel( JSwitchLabel self )
    {
	JExpression expr = self.expr();
	if (expr != null) {
	    expr.accept(this);
	}
    } // visitSwitchLabel

    public void visitTryCatchStatement(JTryCatchStatement self)
    {
	JBlock tryClause = self.tryClause();
	JCatchClause[] catchClauses = self.catchClauses();

	tryClause.accept(this);
	for (int i = 0; i < catchClauses.length; i++) {
	    catchClauses[i].accept(this);
	}
    } // visitTryCatchStatement

    public void visitTryFinallyStatement( JTryFinallyStatement self )
    {
	JBlock tryClause = self.tryClause();
	JBlock finallyClause = self.finallyClause();
	tryClause.accept(this);
	if (finallyClause != null) {
	    finallyClause.accept(this);
	}
    } // visitTryFinallyStatement

    public void visitSynchronizedStatement(JSynchronizedStatement self)
    {
	JExpression cond = self.cond();
	JBlock body = self.body();
	cond.accept(this);
	body.accept(this);
    } // visitSynchronizedStatement

    public void visitReturnStatement( JReturnStatement self )
    {
	JExpression expr = self.expr();
	if (expr != null) {
	    expr.accept(this);
	}
    } // visitReturnStatement

    public void visitThrowStatement( JThrowStatement self )
    {
	JExpression expr = self.expr();
	expr.accept(this);
    } // visitThrowStatement

    public void visitLabeledStatement( JLabeledStatement self )
    {
	String label = self.getLabel();
	JStatement stmt = self.stmt();
	stmt.accept(this);
    } // visitLabeledStatement

    // !FIXME! method call?
    public void visitExplicitConstructorInvocation
	(JExplicitConstructorInvocation self)
    {
	JExpression prefix = self.prefix();
	String ident = self.ident();
	JExpression[] params = self.params();

	if (prefix != null && !self.isPrefixSynthesized()) {
	    prefix.accept(this);
	}

	visitArgs(params);
    }

    public void visitMethodCallExpression( JMethodCallExpression self )
    {
	calledMethods.add(self);
	// String ident = self.ident();
	JExpression[] args = self.args();
	JExpression prefix = self.prefix();
	// JNameExpression sourceName = self.sourceName();

	// if possible, print as it appeared in the source file.
	if (prefix != null) {
	    prefix.accept(this);
	}
	visitArgs(args);
    } // visitMethodCallExpression

    public void visitAddExpression( JAddExpression self )
    {
	visitBinaryExpression( self, "+" );
    } // visitAddExpression

    public void visitConditionalAndExpression ( JConditionalAndExpression self )
    {
	visitBinaryExpression( self, "&&" );
    } // visitConditionalAndExpression

    public void visitConditionalOrExpression ( JConditionalOrExpression self )
    {
	visitBinaryExpression( self, "||" );
    } // visitConditionalOrExpression

    public void visitDivideExpression( JDivideExpression self )
    {
	visitBinaryExpression( self, "/" );
    } // visitDivideExpression

    public void visitMinusExpression( JMinusExpression self )
    {
	visitBinaryExpression( self, "-" );
    } // visitMinusExpression

    public void visitModuloExpression( JModuloExpression self )
    {
	visitBinaryExpression( self, "%" );
    } // visitModuloExpression

    public void visitMultExpression( JMultExpression self )
    {
	visitBinaryExpression( self, "*" );
    } // visitMultExpression

    protected void visitBinaryExpression( JBinaryExpression self, String oper )
    {
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    } // visitBinaryExpression

    public void visitBitwiseExpression( JBitwiseExpression self )
    {
	//   int oper = self.oper();
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    } // visitBitwiseExpression

    public void visitShiftExpression(JShiftExpression self)
    {
	//    int oper = self.oper();
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    } // visitShiftExpression

    public void visitAssignmentExpression( JAssignmentExpression self )
    {
	JExpression left = self.left();
	JExpression right = self.right();

	assignedFields.add(left);
	left.accept(this);
	right.accept(this);
    } // visitAssignmentExpression

    public void visitCompoundAssignmentExpression
	(JCompoundAssignmentExpression self) 
    {
	int oper = self.oper();
	JExpression left = self.left();
	JExpression right = self.right();

	if( left instanceof JClassFieldExpression ) {
	    assignedFields.add(left);
	} else if( left instanceof JArrayAccessExpression ) {
	    assignedFields.add(left);
	    JExpression prefix = ((JArrayAccessExpression)left).prefix();
	    if (prefix instanceof JClassFieldExpression) {
		JExpression accessor 
		    = ((JArrayAccessExpression)left).accessor();
		accessor.accept(this);
	    }
	}
	left.accept(this);
	right.accept(this);
    } // visitCompoundAssignmentExpression

    public void visitPostfixExpression( JPostfixExpression self )
    {
	JExpression expr = self.expr();
	if( expr instanceof JClassFieldExpression ) {
	    assignedFields.add(expr);
	} else if( expr instanceof JArrayAccessExpression ) {
	    assignedFields.add(expr);
	    JExpression arrayRef = ((JArrayAccessExpression)expr).prefix();
	    if (arrayRef instanceof JClassFieldExpression) {
		JExpression accessor 
		    = ((JArrayAccessExpression)expr).accessor();
		accessor.accept(this);
	    }
	} else {
	    expr.accept(this);
	}
    } // visitPostfixExpression

    public void visitPrefixExpression( JPrefixExpression self )
    {
	JExpression expr = self.expr();
	if( expr instanceof JClassFieldExpression ) {
	    assignedFields.add(expr);
	} else if( expr instanceof JArrayAccessExpression ) {
	    assignedFields.add(expr);
	    JExpression arrayRef = ((JArrayAccessExpression)expr).prefix();
	    if (arrayRef instanceof JClassFieldExpression) {
		JExpression accessor 
		    = ((JArrayAccessExpression)expr).accessor();
		accessor.accept(this);
	    }
	} else {
	    expr.accept(this);
	}
    } // visitPrefixExpression

    public void visitLocalVariableExpression( JLocalVariableExpression self )
    {
	//    String ident = self.ident();
    } // visitLocalVariableExpression

    public void visitEqualityExpression( JEqualityExpression self )
    {
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    } //visitEqualityExpression

    public void visitRelationalExpression( JRelationalExpression self )
    {
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    } // visitRelationalExpression

    public void visitNameExpression( JNameExpression self )
    {
	//    JExpression prefix = self.sourcePrefix();
	// String ident = self.sourceIdent();

	accessedFields.add(self);
	//    System.out.println(ident);
	//    if (prefix != null)
	//      prefix.accept(this);
    } // visitNameExpression

    public void visitParenthesedExpression( JParenthesedExpression self )
    {
	JExpression expr = self.expr();
	expr.accept(this);
    } // visitParenthesedExpression

    public void visitCastExpression(JCastExpression self)
    {
	JExpression expr = self.expr();
	//    CType dest = self.getType();
	expr.accept(this);
    } // visitCastExpression

    public void visitNewObjectExpression( JNewObjectExpression self )
    {
	//    CType type = self.getType();
	JExpression[] params = self.params();
	//    print(type);
	visitArgs(params);
    } // visitNewObjectExpression

    public void visitNewAnonymousClassExpression
	( JNewAnonymousClassExpression self )
    {
	// this happens when type checking the anonymous class
    } // visitNewAnonymousClassExpression

    public void visitNewArrayExpression( JNewArrayExpression self ) {
	//    CType type = self.getType();
	JArrayDimsAndInits dims = self.dims();
	dims.accept(this);
    } // visitNewArrayExpression

    public void visitArrayDimsAndInit( JArrayDimsAndInits self )
    {
	// Only need to traverse the initializer
	JArrayInitializer init = self.init();
	if (init != null)
	    init.accept(this);

    } // visitArrayDimsAndInit

    public void visitArrayInitializer( JArrayInitializer self )
    {
	JExpression[] elems = self.elems();
	for (int i = 0; i < elems.length; i++)
	    elems[i].accept(this);
    } // visitArrayInitializer

    public void visitArrayAccessExpression( JArrayAccessExpression self )
    {
	JExpression prefix = self.prefix();
	JExpression accessor = self.accessor();
	//    prefix.accept(this);
	accessedFields.add(prefix);
	accessor.accept(this);
    } // visitArrayAccessExpression

    public void visitArrayLengthExpression( JArrayLengthExpression self )
    {
	// JExpression prefix = self.prefix();
	// prefix.accept(this);
	// print(".length");
    } // visitArrayLengthExpression

    public void visitUnaryExpression( JUnaryExpression self )
    {
	//    int oper = self.oper();
	JExpression expr = self.expr();
	if (expr != null)
	    expr.accept(this);
    } // visitUnaryExpression

    // cast expression
    public void visitUnaryPromoteExpression( JUnaryPromote self )
    {
	JExpression expr = self.expr();
	//      CType type = self.getType();
	expr.accept(this);
    } // visitUnaryPromoteExpression

    public void visitConditionalExpression( JConditionalExpression self )
    {
	JExpression cond = self.cond();
	JExpression left = self.left();
	JExpression right = self.right();
	cond.accept(this);
	left.accept(this);
	right.accept(this);
    } // visitConditionalExpression

    public void visitInstanceofExpression( JInstanceofExpression self ) {
	JExpression expr = self.expr();
	//    CType dest = self.dest();
	expr.accept(this);
    } // visitInstanceofExpression

    public void visitThisExpression( JThisExpression self )
    {
	JExpression prefix = self.prefix();
	if (prefix != null)
	    prefix.accept(this);
    } // visitThisExpression

    public void visitSuperExpression( JSuperExpression self )
    {
	//    print("super");
    } // visitSuperExpression

    public void visitTypeNameExpression( JTypeNameExpression self )
    {
    } // visitTypeNameExpression

    public void visitCatchClause( JCatchClause self )
    {
	JBlock body = self.body();
	body.accept(this);
    } // visitCatchClause

    public void visitStringLiteral( JStringLiteral self)
    {
    } // visitStringLiteral

    public void visitOrdinalLiteral( JOrdinalLiteral self )
    {
    } // visitOrdinalLiteral

    public void visitNullLiteral( JNullLiteral self )
    {
    } // visitNullLiteral

    public void visitBooleanLiteral( JBooleanLiteral self )
    {
    } // visitBooleanLiteral

    public void visitCharLiteral( JCharLiteral self )
    {
    } // visitCharLiteral

    public void visitRealLiteral(JRealLiteral self)
    {
    } // visitRealLiteral

    public void visitTopLevelMethodDeclaration(MJTopLevelMethodDeclaration self)
    {
	// String ident = self.ident();
	JBlock body = self.body();
	visitTLMethodBody(body);
    }
    public void visitTLMethodBody(JBlock body) {
	if (body != null) {
	    body.accept(this);
	}
    }
    public void visitClassBlock(JClassBlock self) {
	visitBlockStatement( self );
    }
    public void visitTypeDeclarationStatement(JTypeDeclarationStatement self) {
	JTypeDeclarationType decl = self.decl();
	decl.accept(this);
    }
    public void visitFieldExpression(JClassFieldExpression self) {
	accessedFields.add(self);
    }

    public void visitFormalParameters(JFormalParameter parm1) {
	// skip formals
    }
    public void visitClassExpression( JClassExpression self ) {
    }

    protected void acceptAll( ArrayList all )
    {
	Iterator iter = all.iterator();
	while( iter.hasNext() ) {
	    ((JPhylum) iter.next()).accept(this);
	}
    } // acceptAll

    protected void visitArgs( JExpression[] args )
    {
	if (args != null) {
	    for (int i = 0; i < args.length; i++) {
		args[i].accept(this);
	    }
	}
    } // visitArgs

    public void visitJmlLoopStatement( JmlLoopStatement self ) {
	if (self.hasAssertionCode()) {
	    self.assertionCode().accept(this);
	} else {
            self.stmt().accept(this);
        }
    }

    public void visitJmlAssignmentStatement( JmlAssignmentStatement self ) {
        self.assignmentStatement().accept(this);
    }

    public void visitJmlNondetChoiceStatement( JmlNondetChoiceStatement self ) {
	JBlock[] alternativeStatements = self.alternativeStatements();
	for( int i = 0; i < alternativeStatements.length; i++ ) {
	    alternativeStatements[i].accept(this);
	}
    }
    public void visitJmlNondetIfStatement( JmlNondetIfStatement self ) {
	JmlGuardedStatement[]  guardedStatements = self.guardedStatements();
	for( int i = 0; i < guardedStatements.length; i++ ) {
	    guardedStatements[i].accept(this);
	}
    }
    public void visitJmlGuardedStatement( JmlGuardedStatement self ) {
	JStatement[] statements = self.statements();
	for( int i = 0; i < statements.length; i++ ) {
	    statements[i].accept(this);
	}
    }
    public void visitJmlRelationalExpression( JmlRelationalExpression self ) 
    {
	JExpression left = self.left();
	JExpression right = self.right();
	left.accept(this);
	right.accept(this);
    }
    public void visitJmlAssumeStatement( JmlAssumeStatement self ) 
    {
    }
    public void visitJmlAssertStatement( JmlAssertStatement self ) 
    {
    }
    public void visitJmlElemTypeExpression(JmlElemTypeExpression self) 
    {
	self.specExpression().accept(this);
    }
    public void visitJmlSpecStatement(JmlSpecStatement self) 
    {
	self.specCase().accept(this);
    }
    public void visitJmlGeneralSpecCase(JmlGeneralSpecCase self) 
    {
	if (self.hasSpecBody()) {
	    self.specBody().accept(this);
	}
    }
    public void visitJmlGenericSpecCase(JmlGenericSpecCase self) 
    {
	visitJmlGeneralSpecCase(self);
    }
    public void visitJmlNormalSpecCase(JmlNormalSpecCase self) 
    {
	visitJmlGeneralSpecCase(self);
    }
    public void visitJmlExceptionalSpecCase(JmlExceptionalSpecCase self) 
    {
	visitJmlGeneralSpecCase(self);
    }
    public void visitJmlAbruptSpecCase(JmlAbruptSpecCase self) 
    {
	visitJmlGeneralSpecCase(self);
    }
    public void visitJmlSpecBody(JmlSpecBody self) 
    {
	if(self.isSpecClauses()) {
	    JmlSpecBodyClause[] specClauses = self.specClauses();
	    for (int i=0; i<specClauses.length; i++) {
		if (specClauses[i] instanceof JmlAssignableClause) {
		    specClauses[i].accept(this);
		}
	    }
	} else {
	    JmlGeneralSpecCase[] specCases = self.specCases();
	    for (int i=0; i<specCases.length; i++) {
		specCases[i].accept(this);
	    }
	}
    }
    public void visitJmlGenericSpecBody(JmlGenericSpecBody self) 
    {
	visitJmlSpecBody(self);
    }
    public void visitJmlNormalSpecBody(JmlNormalSpecBody self) 
    {
	visitJmlSpecBody(self);
    }
    public void visitJmlExceptionalSpecBody(JmlExceptionalSpecBody self) 
    {
	visitJmlSpecBody(self);
    }
    public void visitJmlAbruptSpecBody(JmlAbruptSpecBody self) 
    {
	visitJmlSpecBody(self);
    }
    public void visitJmlAssignableClause( JmlAssignableClause self ) 
    {
	JmlStoreRef[] storeRefs = self.storeRefs();
	for (int i=0; i<storeRefs.length; i++) {
	    if (storeRefs[i] instanceof JmlStoreRefExpression) {
		JExpression expr 
		    = ((JmlStoreRefExpression)storeRefs[i]).expression();
		assignedFields.add(expr);
	    }
	}
    }
    public void visitJmlDebugStatement( JmlDebugStatement self ) 
    {
    }
    public void visitJmlSetStatement( JmlSetStatement self ) {
        self.assignmentExpression().accept(this);
    }
    public void visitJmlRefiningStatement( JmlRefiningStatement self ) {
	self.specStatement().accept(this);
	self.body().accept(this);
    }
    public void visitJmlUnreachableStatement( JmlUnreachableStatement self ) 
    {
    }
    public void visitJmlHenceByStatement( JmlHenceByStatement self ) 
    {
    }
    public void visitJmlTypeExpression( JmlTypeExpression self ) 
    {
    }
    public void visitMathModeExpression( MJMathModeExpression self )
    { 
    }
    public void visitJmlClassDeclaration(JmlClassDeclaration self) {
	visitClassBody( self );
    }
    public void visitJmlTypeOfExpression( JmlTypeOfExpression self ) 
    {
	self.specExpression().accept(this);
    }
    public void visitJmlSpecExpression(JmlSpecExpression self) 
    {
	self.expression().accept(this);
    }
    public void visitJmlPredicate(JmlPredicate self) 
    {
    }
    public void visitJmlPredicateKeyword(JmlPredicateKeyword self) 
    {
    }
    public void visitJmlMethodDeclaration( JmlMethodDeclaration self ) {
    }
    public void visitJmlFieldDeclaration( JmlFieldDeclaration self ) {
	JVariableDefinition variable = self.variable();
	long modifiers = variable.modifiers();
	JExpression expr = variable.getValue();

	if (expr != null) {
	    expr.accept(this);
	}
        if (self.hasAssertionCode()) {
            self.assertionCode().accept(this);
        }
    }
    protected void visitClassBody( JmlTypeDeclaration self ) 
    {
	JPhylum[] fieldsAndInits = self.fieldsAndInits();
	for (int i = 0; i < fieldsAndInits.length ; i++) {
	    fieldsAndInits[i].accept(this);
	}

	// No side effects unless a method is called or class instantiated
	// acceptAll( self.inners() );
	// acceptAll( self.methods() );
    }
    protected void acceptAll( JPhylum[] all ) {
	if (all != null) {
	    for (int i = 0; i < all.length; i++) {
		all[i].accept(this);
	    }
	}
    }

    protected ArrayList assignedFields = null;
    protected ArrayList accessedFields = null;
    protected ArrayList calledMethods = null;
}
