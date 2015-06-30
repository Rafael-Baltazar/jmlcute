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
 * $Id: JmlStoreRefExpression.java,v 1.20 2006/08/15 15:08:03 wahlst Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.*;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;

/**
 * An AST node class for JML store reference expressions.
 * The production rule for the store reference expressions,
 * <tt>store-ref-expression</tt> is defined as follows.
 *
 * <pre>
 *  store-ref-expression ::= store-ref-name [ store-ref-name-suffix ] ...
 *  store-ref-name ::= ident | "super" | "this"
 *  store-ref-name-suffix ::= "." ident | "this" | "[" spec-array-ref-expr "]"
 *  spec-array-ref-expr ::= spec-expression
 *    | spec-expression ".." spec-expression
 *    | "*"
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.20 $
 */
 
public class JmlStoreRefExpression extends JmlStoreRef {

    //---------------------------------------------------------------------
    // CONSTRUCTORS	
    //---------------------------------------------------------------------

    public JmlStoreRefExpression( TokenReference where, 
				  JmlName[] names ) {
	super( where );
	this.names = names;
	String n = "";
	for (int i=0; i<names.length; i++) {
	    if ( i != 0 && !names[i].isSpecArrayRefExpr() ) {
		n += ".";
	    }
	    n += names[i].getName();
	}
	this.name = n;
    }

    // -------------------------------------------------------------
    // ACCESSORS
    // -------------------------------------------------------------

    public boolean isStoreRefExpression() {
	return true;
    }

    public String getName() {
	return name;
    }

    public JmlName[] names() {
	return names;
    }

    /** Returns the type of this store ref expression. If this store ref
     * expression denotes a spec array ref expression, e.g., a[*], its
     * element type is returned. This method must be called after type
     * checking. */
    public CType getType() {
	return expression.getType();
    }

    /** Returns an expression object corresponding to this store 
     * ref expression. This method must be called after type checking. */
    public JExpression expression() {
        return expression;
    }

    /** Returns true iff the store ref expression is the pseudo 
     *  variable 'super'. 
     *  This method must be called after type checking. */
    public boolean isSuperExpression() {
        return (expression instanceof JSuperExpression)
	    && names.length == 1;
    }

    /** Returns true iff the store ref expression is the 
     *  receiver 'this'. 
     *  This method must be called after type checking. */
    public boolean isThisExpression() {
        return (expression instanceof JThisExpression)
	    && names.length == 1;
    }

    /** Returns true iff the store ref expression accesses a field
     *  of a model field.
     *  This method must be called after type checking. */
    public boolean isInvalidModelFieldRef() {
	if (expression instanceof JClassFieldExpression) {
	    JClassFieldExpression fieldExpr = (JClassFieldExpression)expression;
	    JExpression prefix = fieldExpr.prefix();
	    while (prefix != null) {
		if (prefix instanceof JClassFieldExpression) {
		    fieldExpr = (JClassFieldExpression)prefix;
		    CFieldAccessor fieldA = fieldExpr.getField();
		    if (fieldA instanceof JmlSourceField) {
			JmlSourceField field = (JmlSourceField)fieldA;
			if (field.jmlAccess().isModel()) {
			    return true;
			}
		    }
		    prefix = fieldExpr.prefix();
		} else {
		    break;
		}
	    }
	}

	return false;
    }

    public String toString() {
	return getName();
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    /** Returns true if the given argument refers to a model field.
     * This method must be called after typechecking.
     * 
     * <pre><jml>
     *  requires (* called after typechecking *);
     * </jml></pre>
     */
    public boolean isModelField() {
        CFieldAccessor field = getField();
        return field != null && 
            (field instanceof JmlModifiable) &&
            ((JmlModifiable)field).isModel();
    }

    /** Returns true if the store-ref expression refers to a field 
     *  of the current receiver (this).
     */
    public boolean isFieldOfReceiver() {
	return (names.length == 1 && names[0].isIdent())
	    || (names.length == 2 && names[0].isThis() && names[1].isIdent());
    }

    /** Returns <code>CFieldAccessor</code> of this store ref expression
     * if it denotes denotes a class field. 
     * Otherwise, return <code>null</code>.
     * This method must be called after typechecking.
     * 
     * <pre><jml>
     *  requires (* called after typechecking *);
     * </jml></pre>
     */
    public CFieldAccessor getField() {
        if (expression instanceof JClassFieldExpression) {
            return ((JClassFieldExpression) expression).getField();
        }
        return null;
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    //@ also
    //@ ensures \result == !(expression instanceof JLocalVariableExpression);
    public /*@ pure @*/ boolean isLocalVarReference() {
	return (expression instanceof JLocalVariableExpression);
    }

    /**
     * Typechecks this store reference in the given visibility,
     * <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @return a desugared store reference
     * @exception PositionedError if the check fails 
     */
    public JmlStoreRef typecheck( CExpressionContextType context,
                                  long privacy )
	throws PositionedError 
    {
	expression = null;
        isFieldsOf = false;
	for (int i = 0; i < names.length; i++) {
	    // check element, esp. spec-array-ref-expr
	    names[i] = names[i].typecheck(context);

	    if (isFieldsOf) {
		check( context, 
		       false,
		       JmlMessages.MISPLACED_DOT_STAR, 
		       name );
	    }
	    
	    // build complete name expression, e.g., this.x[0].
	    TokenReference where = names[i].getTokenReference();
	    if (names[i].isIdent()) {
		expression = new JNameExpression(where, expression, 
						 names[i].ident());
	    } else if (names[i].isThis()) {
		expression = new JThisExpression(where, expression);
	    } else if (names[i].isSuper()) {
		// super is guranteed to be the first by the parser
		expression = new JSuperExpression(where);
	    } else if (names[i].isSpecArrayRefExpr()) {
		// translate spec-array-ref-expr to array-access-expr
		// for typechecking purpose.
		expression = new JArrayAccessExpression(where, expression, 
		         new JOrdinalLiteral(where, "0")); // dummy value
	    } else if (names[i].isFields()) {
		isFieldsOf = true;
	    } else {
		throw new RuntimeException("Reached unreachable!");
	    }
	}
	
	// check the whole name if non-null
	if (expression != null) {
	    expression = expression.typecheck(context);

	    if (isFieldsOf) {
		final CType expType = expression.getType();
		check( context, 
		       expType.isReference(),
		       JmlMessages.NOT_REFERENCE_EXPRESSION, 
		       expType );
	    }

            // purity and visibility check
            JmlExpressionChecker.perform(context, privacy, expression);
        }
	
    	return this;
    }

    /**
     * Typechecks this store reference in the given visibility,
     * <code>privacy</code>, and mutates the context,
     * <code>context</code>, to record information gathered during
     * typechecking.
     *
     * @param context the context in which this store reference appears
     * @param privacy the visibility in which to typecheck
     * @param type the type whose fields this store reference is supposed
     *             to denote
     * @return a desugared store reference
     * @exception PositionedError if the check fails 
     */
    public JmlStoreRef typecheck( CExpressionContextType context, 
                                  long privacy,
                                  CType type )
	throws PositionedError 
    {
	// We indirectly typecheck by building a term of the form
	// "$jml.n1.n2..." and type-checking it in a temp context
	// with a local variable $jml of the given argument type.

	PositionedError error = null;
	JExpression exp 
	    = new JNameExpression(getTokenReference(), null, "$jml");
	for (int i = 0; i < names.length; i++) {
	    names[i] = names[i].typecheck(context);
	    
	    // build complete expression, e.g., $jml.n1...nm[0].
	    TokenReference where = names[i].getTokenReference();
	    if (names[i].isIdent()) {
		exp = new JNameExpression(where, exp, names[i].ident());
	    }
	    else if (names[i].isSpecArrayRefExpr()) {
		// translate it (e.g., [*], [0..3]) to array-access-expr 
		exp = new JArrayAccessExpression(where, exp, 
		          new JOrdinalLiteral(where, "0")); // dummy value 0
	    }
	    else if (names[i].isThis()) {
		error = new PositionedError(names[i].getTokenReference(),
					    JmlMessages.THIS_NOT_ALLOWED);
	    }
	    else if (names[i].isSuper()) {
		error = new PositionedError(names[i].getTokenReference(),
					    JmlMessages.SUPER_NOT_ALLOWED);
	    }
	    else // no other type of names
		throw new RuntimeException("Reached unreachable!");
	}
	
	if (error != null) {
	    context.reportTrouble(error);
	    return this;
	}

	// now, typecheck the exp in a temp context with the prefix
	// $jml defined as a local var with proper type.
	CFlowControlContextType outer = context.getFlowControlContext();
	CFlowControlContextType newBody = 
	    outer.createFlowControlContext(1,getTokenReference());
	
	try {
	    JVariableDefinition var = new JVariableDefinition(
	       getTokenReference(), 0, type, "$jml", null);
	    newBody.addVariable(var);
	    newBody.initializeVariable(var);
	} catch( UnpositionedError e ) {
	    throw new RuntimeException("Reached unreachable!");
	}

	CExpressionContextType ectx = newBody.createExpressionContext();
	exp = exp.typecheck(ectx);

        // purity and visibility check
        JmlExpressionChecker.perform(ectx, privacy, exp);

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
	    ((JmlVisitor)p).visitJmlStoreRefExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * The initial name and name suffixes of this
     * store-ref-expression.  */
    private final JmlName[] names;

    private /*@ spec_public @*/ JExpression expression;
    private boolean isFieldsOf = false;

    private final String name;

}// JmlStoreRefExpression
