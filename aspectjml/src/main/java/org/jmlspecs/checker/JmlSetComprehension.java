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
 * $Id: JmlSetComprehension.java,v 1.10 2006/02/02 16:42:21 chalin Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.CompilationAbortedError;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * An AST node class for JML's set comprehension notation. The set
 * comprehension notation can be used to succinctly define sets. For
 * example, <code>{Integer i | myIntSet.has(i) && i != null &&
 * i.getInteger() > 0}</code> denotes the subset of non-null
 * <code>Integer</code> objects found in the set <code>myIntSet</code>
 * whose value is positive. The syntax of JML limits set
 * comprehensions so that the following the vertical
 * bar(<code>|</code>) is always invocation of the <code>has</code> or
 * <code>contains</code> method of some set on the variable
 * declared. This restriction is used to avoid the Russell's
 * paradox. The syntax for JML's set comprehension notation is as
 * follows.
 *
 * <pre>
 *  set-comprehension ::= "{" [bound-var-modifiers] type-spec quantified-var-declarator "|"
 *      set-comprehension-pred "}"
 *  set-comprehension-pred ::= spec-primary-expr [ "." ident ] ...
 *      "has" "(" ident ")" "&&" predicate
 *  quantified-var-declarator ::= ident [ dims ]
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.10 $
 */

public class JmlSetComprehension extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlSetComprehension( TokenReference where, 
				long modifiers,
				CType type,
				CType memberType, String ident,
				JExpression supersetPred, 
				JmlPredicate predicate ) {
	super( where );
	this.modifiers = modifiers;
	this.type = type;
	this.memberType = memberType;
	this.ident = ident;
	this.supersetPred = supersetPred;
	this.predicate = predicate;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ String ident() {
	return ident;
    }

    public /*@ pure @*/ CType memberType() {
	return memberType;
    }

    public /*@ pure @*/ JExpression supersetPred() {
	return supersetPred;
    }

    public /*@ pure @*/ JmlPredicate predicate() {
	return predicate;
    }

    public /*@ pure @*/ CType getType() {
	return type;
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
     * @exception PositionedError if the check fails 
     */
    public JExpression typecheck( CExpressionContextType context ) 
	throws PositionedError 
    {
        // find JMLObjectSet and JMLValueSet
        CType objectSet = null;
        CType valueSet = null;
        try {
            objectSet = CTopLevel.getTypeRep(TN_JMLOBJECTSET, true);
            valueSet = CTopLevel.getTypeRep(TN_JMLVALUESET, true);
        }
        catch (CompilationAbortedError e) {
            System.err.println("jml: can't find a model type " +
                               "JMLObjectSet or JMLValueSet!");
	    throw e;
        }

	// is type well-formed and is it either JMLObjectSet or
	// JMLValueSet?
	try {
	    type = type.checkType( context );
            check(context, type.equals(objectSet) || type.equals(valueSet),
                  JmlMessages.SET_COMPREHENSION_TYPE, type);
        }
	catch (UnpositionedError e) {
	    context.reportTrouble(
	       new PositionedError(getTokenReference(),
				   JmlMessages.TYPE_UNKNOWN, type));
	}

	// is member type well-formed?
	try {
	    memberType = memberType.checkType( context );
        }
	catch (UnpositionedError e) {
	    context.reportTrouble(
	       new PositionedError(getTokenReference(),
				   JmlMessages.TYPE_UNKNOWN, memberType));
	}

	// is the member type a reference type?
	check ( context,
		memberType.isReference(),
		JmlMessages.NOT_REFERENCE_SET_MEMBER_TYPE );

	// for a value set, the member type must be a subtype of JMLType
        if (type.equals(valueSet)) {
            CType jmlType = null;
            try {
                jmlType = CTopLevel.getTypeRep(TN_JMLTYPE, true);
            }
            catch (CompilationAbortedError e) {
                System.err.println("jml: can't find a model type JMLType!");
		throw e;
            }         
            check(context,
                  memberType.isAlwaysAssignableTo(jmlType),
                  JmlMessages.NOT_JMLTYPE_SET_MEMBER_TYPE, memberType);
        }

	// is the superset predicate of the form exp.has(ident)?
	check ( context,
		isSupersetPredWellFormed(),
		JmlMessages.ILL_FORMED_SET_COMPREHENSION );

	// create temp contexts for checking the expression
	CFlowControlContextType fcContext = context.getFlowControlContext();
	CFlowControlContextType newBlock = 
	    fcContext.createFlowControlContext(1,getTokenReference());

	try {
	    JVariableDefinition var 
		= new JVariableDefinition(getTokenReference(), 0,
					  memberType, ident, null);
	    newBlock.addVariable(var);
	    var.typecheck(newBlock);

	    // make it initialized to prevent uninit. var ref errors
	    newBlock.initializeVariable(var);
	} catch( UnpositionedError e ) {
	    throw e.addPosition( getTokenReference() );
	}

	if (!(context instanceof JmlExpressionContext))
	    throw new IllegalArgumentException(
	      "JmlExpressionContext object expected");

	JmlExpressionContext ectx = 
	    JmlExpressionContext.createSameKind(
	       newBlock, (JmlExpressionContext) context);

	// typecheck the superset predicate
	supersetPred = supersetPred.typecheck( ectx );
	check( context, 
	       supersetPred.getType().isBoolean(),
	       JmlMessages.ILL_FORMED_SET_COMPREHENSION );

	// typecheck the predicate
	predicate = (JmlPredicate) predicate.typecheck( ectx );

	// discard temp contexts
	newBlock.checkingComplete();

	return this;
    }

    /** Is the superset predicate structurally well-formed, i.e.,
     * of the form exp.has(ident)?
     */
    private boolean isSupersetPredWellFormed() {
	// is it a method call?
	if (!(supersetPred instanceof JMethodCallExpression))
	    return false;

	JMethodCallExpression ce = (JMethodCallExpression) supersetPred;

	// is it a "has" method call?
	if (!("contains".equals(ce.ident()) || "has".equals(ce.ident())))
	    return false;

	// does the argument match, i.e., is it ident?
	if (ce.args().length != 1 
	    || !(ce.args()[0] instanceof JNameExpression))
	    return false;
	JNameExpression ne = (JNameExpression) ce.args()[0];
	return ident.equals(ne.getName()) ? true : false;
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
	    ((JmlVisitor)p).visitJmlSetComprehension(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private long modifiers; 
    private CType type;
    private CType memberType;
    private String ident;
    private JExpression supersetPred;
    private JmlPredicate predicate;

}// JmlSetComprehension
