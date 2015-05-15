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
 * $Id: JmlSignalsClause.java,v 1.18 2006/11/27 15:36:48 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * A JML AST node class for the <code>signals</code> clause. The syntax
 * for the <code>signals</code> is defined as follows.
 *
 * <pre>
 *  signals-clause ::= signals-keyword "(" referencetype [ ident ] ")"
 *      [ pred-or-not ] ";"
 *  signals-keyword ::= "signals" | "signals_reduantly" | "exsures"
 *    | "exsures_redundantly"
 *  pred-or-not ::= predicate | "\not_specified"
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.18 $
 */

public class JmlSignalsClause extends JmlPredicateClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires type != null;
    //@ requires notSpecified ==> pred == null;
    public JmlSignalsClause( TokenReference where,
			     boolean isRedundantly, 
			     CType type,
			     String ident, 
			     JmlPredicate pred,
			     boolean notSpecified ) {
	super( where, isRedundantly, pred );
	this.type = type;
	this.ident = ident;
	this.notSpecified = notSpecified;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ int preferredOrder() {
	return PORDER_SIGNALS_CLAUSE;
    }

    public /*@ pure @*/ CType type() {
	return type;
    }

    public /*@ pure @*/ String ident() {
	return ident;
    }

    /**
     * Indicates whether this clause has the predicate
     * <code>not_specified</code>.  
     *
     * <pre><jml>
     * also
     *   ensures \result == notSpecified;
     * </jml></pre>
     *
     */
    public /*@ pure @*/ boolean isNotSpecified() {
	return notSpecified;
    }

    /**
     * Indicates whether this clause has a predicate.
     *
     * <pre><jml>
     * ensures \result == (predOrNot != null);
     * </jml></pre>
     *
     */
    public /*@ pure @*/ boolean hasPredicate() {
	return predOrNot != null;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isNormalSpecBody() {
	return false;
    }

    /**
     * @return false
     */
    public /*@ pure @*/ boolean isAbruptSpecBody() {
	return false;
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
     * Typechecks this JML clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context, long privacy )
	throws PositionedError
    {
	// verity that the exception type is known?
	try {
	    type = type.checkType( context );
	}
	catch (UnpositionedError e) {
	    // throw e.addPosition(getTokenReference());
	    throw new PositionedError(getTokenReference(),
				      JmlMessages.TYPE_UNKNOWN,
				      type);
	}

	if (!type.isAlwaysAssignableTo(CStdType.Throwable))
	    check( context, false, JmlMessages.BAD_TYPE_IN_SIGNALS,
		   type.toVerboseString() );


	// typecheck the expression if it exists
	if (!isNotSpecified() && hasPredicate()) {

	    // check the predicate in a context with the parameter in scope
	    CFlowControlContextType inside = context;

	    if (ident != null) {
		inside = context.createFlowControlContext(1,getTokenReference());
		inside.setReachable( true );
		try {
		    JVariableDefinition var 
			= new JVariableDefinition(getTokenReference(), 0, type,
						   ident, null);
		    inside.addVariable( var );
		    inside.addFANonNull( var );
		    inside.initializeVariable(var);
		} catch( UnpositionedError e ) {
		    throw e.addPosition( getTokenReference() );
		}
	    }

            super.typecheck(inside, privacy);

	    if (ident != null) {
		inside.checkingComplete();
	    }

	} 

	// verify that the exception is defined in the throw list, but
	// only checked exceptions need to be verified.
 	// This check is performed after typechecking the expression so that
 	// we can test whether the expression is a constant false literal
 	// (which information is only available after typechecking).
	if (type.isCheckedException()) {
            CType ctype = CStdType.RuntimeException;
            //@ assert ctype != null;
	    boolean declared =
                // true if ctype is a subtype of RunTimeException ...
                ctype.isAlwaysAssignableTo(type)
                // ... or is a supertype of RuntimeException
                // i.e., (is Throwable or Exception).
                || type.isAlwaysAssignableTo(ctype);
            if (!declared) {
                CClassType[] checked = context.getCMethod().throwables();
                for (int i = 0; i < checked.length; i++) {
                    if (type.isAlwaysAssignableTo(checked[i]) ||
                        checked[i].isAlwaysAssignableTo(type)) {
                        declared = true;
                        break;
                    }
                }
            }
 	    if (!declared) {
 		// Even if the exception is not declared, we won't complain
 		// if the predicate has a constant false value.
 		if (hasPredicate()) {
                    JExpression j = predOrNot.specExpression().expression();
                    if (j instanceof JBooleanLiteral &&
                        !((JBooleanLiteral)j).booleanValue()) return;
 		}
 	    }
 	    
 	    // check if the method is a PC method --- [[[hemr]]]
 	    boolean canCheck = true;
 	    List<JavaMethod> javaMeths = AspectUtil.getInstance().getAllDeclaredJavaMethodsInFile(context.getCMethod().getOwnerName().replace("/", "."));
 	    String jmlMeth = context.getCMethod().getIdent()+AspectUtil.generateMethodParameters(context.getCMethod().parameters());
 	    for (Iterator<JavaMethod> iterator = javaMeths.iterator(); iterator.hasNext();) {
			JavaMethod currentJavaMeth = iterator.next();
			String currentMethSig = currentJavaMeth.getName()+AspectUtil.generateMethodParameters(currentJavaMeth.getParameters(), false);
			if(jmlMeth.equals(currentMethSig)){
				if(QDoxUtil.iPCXCS(currentJavaMeth)){
					canCheck = false;
				}
			}
		}
 	 
 	    if(canCheck){
 	    	 check( context, declared, 
 	    			   JmlMessages.UNCAUGHT_EXCEPTION_IN_SIGNALS,
 	    			   type );
 	    }
	}
    }

    /** Returns an appropriate context for checking this clause. */
    protected JmlExpressionContext createContext(
        CFlowControlContextType context) {
        return JmlExpressionContext.createExceptionalPostcondition( context );
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
	    ((JmlVisitor)p).visitJmlSignalsClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    //@ private invariant type != null;
    private CType type;
    private String ident;
    /*@ spec_public @*/ private boolean notSpecified;
}
