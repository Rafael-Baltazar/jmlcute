/*
 * Copyright (C) 2000-2001 Iowa State University
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
 *
 * $Id: JmlSpecQuantifiedExpression.java,v 1.7 2006/11/27 15:36:48 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * An AST node class for JML quantified expressions. JML supports several
 * forms of quantified expressions: universal and existential quantifiers,
 * generalized quantifiers, and a numeric quantifier. They all have the
 * same structural and syntactical forms. The JML syntax for quantified 
 * expressions is described by the production rule, 
 * <tt>spec-quantified-expr</tt>. The production rule 
 * <tt>spec-quantified-expr</tt> is defined as follows.
 *
 * <pre>
 *  spec-quantified-expr ::= "(" quantifier quantified-var-decl ";"
 *      [ [ predicate ] ";" ] spec-expression ")"
 *  quantifier ::= "\forall" | "\exists" | "\max" | "\min" | "\num_of"
 *    | "\product" | "\sum"
 *  quantified-var-decl ::= type-spec quantified-var-declarator
 *      [ "," quantified-var-declarator ] ...
 *  quantified-var-declarator ::= ident [ dims ]
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.7 $
 */

public class JmlSpecQuantifiedExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlSpecQuantifiedExpression( TokenReference where, int oper,
					JVariableDefinition[]
					quantifiedVarDecls,
					JmlPredicate predicate, 
					JmlSpecExpression specExpression ) {
	super( where );
	this.oper = oper;
	this.quantifiedVarDecls = quantifiedVarDecls;
	this.predicate = predicate;
	this.specExpression = specExpression;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isForAll() {
	return oper == OPE_FORALL;
    }

    public /*@ pure @*/ boolean isExists() {
	return oper == OPE_EXISTS;
    }

    public /*@ pure @*/ boolean isMax() {
	return oper == OPE_MAX;
    }

    public /*@ pure @*/ boolean isMin() {
	return oper == OPE_MIN;
    }

    public /*@ pure @*/ boolean isNumOf() {
	return oper == OPE_NUM_OF;
    }

    public /*@ pure @*/ boolean isProduct() {
	return oper == OPE_PRODUCT;
    }

    public /*@ pure @*/ boolean isSum() {
	return oper == OPE_SUM;
    }

    public /*@ pure @*/ int oper(){
        return oper;
    }

    public /*@ pure @*/ JVariableDefinition[] quantifiedVarDecls() {
	return quantifiedVarDecls;
    }

    public /*@ pure @*/ boolean hasPredicate() {
	return predicate != null;
    }

    public /*@ pure @*/ JmlPredicate predicate() {
	return predicate;
    }
    
    public /*@ pure @*/ JmlSpecExpression specExpression() {
	return specExpression;
    }

    public /*@ pure @*/ CType getType() {
	switch (oper) {
	case OPE_FORALL:
	case OPE_EXISTS:
	    return CStdType.Boolean;

	case OPE_NUM_OF:
	    return CStdType.Long;

	case OPE_MAX:
	case OPE_MIN:
	case OPE_PRODUCT:
	case OPE_SUM:
	    return specExpression.getType();
	    
	default:
	    fail( "invalid oper" );
	    break;
	} // end of switch (oper)
	
	//@ unreachable;
	return null;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks the expression and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @return a desugared Java expression
     * @exception PositionedError if the check fails */
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError 
    {
	if (!(context instanceof JmlExpressionContext))
	    throw new IllegalArgumentException(
	      "JmlExpressionContext object expected");

	// create temp context for storing qvar info:
	CFlowControlContextType outer = context.getFlowControlContext();
	CFlowControlContextType newBody = 
	    outer.createFlowControlContext(quantifiedVarDecls.length,
					   getTokenReference());

	// add qvar to new block context
	for (int i = 0; i <  quantifiedVarDecls.length; i++) {
	    JVariableDefinition var = quantifiedVarDecls[i];
	    try {
		newBody.addVariable(var);
		var.typecheck(newBody);

		// make it initialized to prevent uninit. var ref errors
		newBody.initializeVariable(var);
	    } catch( UnpositionedError e ) {
		throw e.addPosition( var.getTokenReference() );
	    }
	}

	JmlExpressionContext qctx = 
	    JmlExpressionContext.createSameKind(
	       newBody, (JmlExpressionContext) context);

	// typecheck range predicate if exists, under new context
	if (predicate != null)
	    predicate = (JmlPredicate) predicate.typecheck( qctx );

	// typecheck the expression part
	//@ assert specExpression != null;
	specExpression = 
	    (JmlSpecExpression) specExpression.typecheck( qctx );
	
	final CType rtype = specExpression.getType();
	if (isForAll() || isExists() || isNumOf()) {
	    // universal, existential or numerical quantifier
	    check( context, 
		   rtype == JmlStdType.Boolean,
		   JmlMessages.NOT_BOOLEAN_IN_QUANTIFIED );
	} else {
	    // generalized qunatifier
	    check( context,
		   rtype.isNumeric(),
		   JmlMessages.NOT_NUMERIC_IN_QUANTIFIED );		   
	}

	// discard temp contexts
	newBody.checkingComplete();

	return this;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlSpecQuantifiedExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private int oper;
    private JVariableDefinition[] quantifiedVarDecls;
    private JmlPredicate predicate;
    private JmlSpecExpression specExpression;

}
