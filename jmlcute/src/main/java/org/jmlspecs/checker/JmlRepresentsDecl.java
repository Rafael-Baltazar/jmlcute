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
 * $Id: JmlRepresentsDecl.java,v 1.18 2005/12/22 20:50:50 darvasa Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * This AST node represents a JML represents declaration annotation.
 * The syntax for the represents declaration is as follows.
 *
 * <pre>
 *  represents-decl ::= represents-keyword store-ref "<-" spec-expression ";"
 *    | represents-keyword store-ref "=" spec-expression ";"
 *    | represetns-keyword store-ref "\such_that" predicate ";"
 *  represents-keyword ::= "represents" | "represents_redundantly"
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.18 $
 */

public class JmlRepresentsDecl extends JmlDeclaration {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Creates a new <code>JmlRepresentsDecl</code> instance.
     *
     * @param where a <code>TokenReference</code> value
     * @param modifiers modifier bit-mask
     * @param redundantly true ==> this is a representsDecl_redundantly 
     *				statement
     * @param storeRef the model variable whose representation is being defined
     * @param specExpression the abstract function that gives the value of 
     *			     <code>storeRef</code> based on its dependees
     */
    public JmlRepresentsDecl( TokenReference where, long modifiers, 
			      boolean redundantly, 
                              JmlStoreRefExpression storeRef, 
			      JmlSpecExpression specExpression ) 
    {
	super( where, modifiers, redundantly );
	this.storeRef = storeRef;
	this.specExpression = specExpression;
	this.predicate = null;
    }

    /**
     * Creates a new <code>JmlRepresentsDecl</code> instance.
     *
     * @param where a <code>TokenReference</code> value
     * @param modifiers modifier bit-mask
     * @param redundantly true ==> this is a representsDecl_redundantly 
     *				statement
     * @param storeRef the model variable whose representation is being defined
     * @param predicate the abstract relation that relates the value of 
     *			<code>storeRef</code> to its dependees
     */
    public JmlRepresentsDecl( TokenReference where, long modifiers, 
			      boolean redundantly, 
                              JmlStoreRefExpression storeRef, 
			      JmlPredicate predicate ) 
    {
	super( where, modifiers, redundantly );
	this.storeRef = storeRef;
	this.specExpression = null;
	this.predicate = predicate;
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the store ref expression of this represents declaration. */
    public JmlStoreRefExpression storeRef() {
        return storeRef;
    }

    /** Returns the spec expression of this represents declaration. 
     * If this declaration uses an abstraction relation, <code>null</code>
     * is returned. */
    public JmlSpecExpression specExpression() {
        return specExpression;
    }

    /** Returns the predicate of this represents declaration. 
     * If this declaration uses an abstraction function, <code>null</code>
     * is returned. */
    public JmlPredicate predicate() {
        return predicate;
    }
	
    /**
     * Indicates whether this represents declaration uses an
     * abstraction function.  
     *
     * <pre><jml>
     * ensures \result <==> specExpression != null;
     * </jml></pre>
     *
     */
    public boolean usesAbstractionFunction() {
	return specExpression != null;
    }

    /**
     * Indicates whether this represents declaration uses an
     * abstraction relations.  
     *
     * <pre><jml>
     * ensures \result <==> predicate != null;
     * </jml></pre>
     *
     */
    public boolean usesAbstractionRelation() {
	return predicate != null;
    }

    /** Returns the identifier of the represented model field. This
     * method can be called before typechecking. But to get the
     * accurate result, one should call the getField method after
     * typechecking.
     */
    public String ident() {
        JmlName[] names = storeRef.names();
        if (names[names.length -1].isIdent()) {
            return names[names.length -1].ident();
        }
        return null;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    /** Returns the JmlSourceField of the model variable that this
     * <code>represents</code> clause specifies for. This method must be
     * called after typechecking. */
    public JmlSourceField getField() {
	JExpression fieldRef = storeRef.expression();
	if (fieldRef instanceof JClassFieldExpression) {
            return (JmlSourceField)
		((JClassFieldExpression)fieldRef).getField();
	} else {
	    return null;
	}
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this depends/represents clause in the context in which it
     * appears. The type checking rules for depends/represents clauses are
     * defined as follows.
     *
     * <p>
     * <ul>
     * <li> Both left-hand side and right-hand side must be type-correct.
     * </li>
     *
     * <li> The store-ref must be a reference to a model field.
     * </li>
     *
     * <li> A non-static clause must not have a static model variable
     * on the left-hand side (i.e., store-ref).
     * </li>
     *
     * <li> 
     * A static clause must appear in the same type where the model variable
     * on the left-hand side is declared.
     * </li>
     *
     * <li> 
     * For a non-static clause, the model variable on the left-hand side 
     * must be declared in the current class, superclasses, interfaces, 
     * or outter classes or interfaces.
     * </li>
     * </ul>
     * </p>
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CContextType context ) throws PositionedError 
    {
	try {
	    enterSpecScope();

            // check modifiers
            checkModifiers(context);

            // check the store-ref part
	    JmlExpressionContext ectx = createContext(context);
	    checkStoreRef(ectx);

            checkRightHandSide(ectx);
            /* rzakhejm begin */
            /* Admissibility check */
    		if (JmlAdmissibilityVisitor.isAdmissibilityCheckEnabled()) {
    			if (!isStatic())
    				JmlAdmissibilityVisitor.checkRepresentsClause(this, ectx);
    			else
    				warn(context, JmlMessages.ADMISSIBILITY_STATICS_NOT_SUPPORTED,
    						usesAbstractionFunction() ? (Object) specExpression() : (Object) predicate());
    		}
            /* rzakhejm end */
	}
	finally {
	    exitSpecScope();
	}
    }

    /** Checks the store ref of this depends/represents clause. 
     * The store ref on the left-hand side must be type-correct 
     * and refer to a model field. If this clause is non-static, 
     * the store ref must refer to a non-static model field. 
     * For static, this clause must appear in the same class (interface) 
     * where the model field on the left-hand side is declared in. 
     * For non-static, this clause must appear in in a type descended 
     * from or nested in the type where the model field (on the left-hand
     * side) is declared.
     */
    protected void checkStoreRef(JmlExpressionContext context ) 
        throws PositionedError {
        // is store ref type-correct?
        storeRef.typecheck(context, privacy());

        // is it a reference to a model field?
        if (!storeRef.isModelField()) {
            check(context, false, JmlMessages.REPRESENTS_NOT_MODEL);
        } else { 

            // A non-static rep can't have a static model variable 
            // on the left-hand side.
            CFieldAccessor field = storeRef.getField();
	    CClass contextOwner = context.getClassContext().getOwnerClass();
	    CClass fieldOwner = field.owner();

            if (!isStatic() && field.isStatic()) {
                check(context, false, JmlMessages.REPRESENTS_STATIC_FIELD);
            } else {
		if (isStatic()) {
		    // A static rep must appear in the same class as the 
		    // model field (on the left-hand side) is declared in.
		    if ( (contextOwner instanceof JmlSourceClass) 
			 && (fieldOwner instanceof JmlSourceClass) )
		    {
			JmlSourceClass contextOwnerClass 
			    = (JmlSourceClass) contextOwner;
			JmlSourceClass fieldOwnerClass 
			    = (JmlSourceClass) fieldOwner;
			check(context, 
			      contextOwnerClass.refines(fieldOwnerClass) 
			      || fieldOwnerClass.refines(contextOwnerClass),
			      JmlMessages.REPRESENTS_STATIC_LOCALITY, 
			      fieldOwner );
		    } else {
			check(context, 
			      contextOwner == fieldOwner,
			      JmlMessages.REPRESENTS_STATIC_LOCALITY, 
			      fieldOwner );
		    }
		} else {

		    // A non-static rep must appear in a type descended 
		    // from or nested in the type where the model field 
		    // (on the left-hand side) is declared.
		    JClassFieldExpression storeRefExpr 
			= (JClassFieldExpression) storeRef.expression();
		    check(context,
			  isInheritedOrOuter(storeRefExpr),
			  JmlMessages.REPRESENTS_LOCALITY, 
			  fieldOwner );
		}
	    }
	}
    }

    /** Performs type-checking of right-hand side of the represents clause. 
     * E.g., typechecks the right-hand side spec-expression (or predicate).
     * For a functional abstraction form, the spec-expression must be
     * assignment-compatible to the model field on the left-hand side.
     */
    protected void checkRightHandSide(JmlExpressionContext context) 
        throws PositionedError 
    {
        long privacy = privacy();

        // check functional abstraction
        if (specExpression != null) {
            specExpression = 
                (JmlSpecExpression) specExpression.typecheck(context, privacy);
            
            // is assignment-compatible?
            CType type = storeRef.expression().getType();
            check(context, 
                  specExpression.isAssignableTo(type),
                  JmlMessages.REPRESENTS_TYPE_MISMATCH,
                  specExpression.getType(),
                  type);
        }

        // check relational abstraction
        if (predicate != null) {
            predicate = (JmlPredicate) predicate.typecheck(context, privacy);
        }
    }

    /** Returns true if the given field expression refers to a field
     * declared in this class, inherited from a superclasse or interface,
     * or defined in an outer class or interface.
     */
    protected static boolean isInheritedOrOuter(JClassFieldExpression field) {
        JExpression prefix = field.prefix();

        // field in this class or inherited one?
        if ((prefix == null) ||
            (prefix instanceof JThisExpression) ||
            (prefix instanceof JSuperExpression)) {
            return true;
        }
        
        // outer field?
        return (prefix instanceof JClassFieldExpression) &&
            JAV_OUTER_THIS.equals(((JClassFieldExpression)prefix).ident());
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
	    ((JmlVisitor)p).visitJmlRepresentsDecl(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * An AST for the storeRef expression of the more abstract variable in
     * this.  */
    protected JmlStoreRefExpression storeRef;

    //@ private invariant specExpression == null <==> predicate != null;
    /*@ private invariant_redundantly 
		specExpression != null <==> predicate == null;
      @*/
    /*@ spec_public @*/ private JmlSpecExpression specExpression;
    /*@ spec_public @*/ private JmlPredicate predicate;

}
