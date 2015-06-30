/*
 * Copyright (C) 2005 Iowa State University
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
 * $Id: JmlSignalsOnlyClause.java,v 1.6 2005/07/11 17:57:45 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * A JML AST node class for the <code>signals_only</code> clause. The syntax
 * for the <code>signals_only</code> is defined as follows.
 *
 * <pre>
 *  signals-only-clause ::= signals-only-keyword name-list ";"
 *                         | signals-only-keyword \nothing ";"
 *  signals-only-keyword ::= "signals_only" | "signals_only_redundantly"
 * </pre>
 *
 * @author Gary T. Leavens
 * @version $Revision: 1.6 $
 */

public class JmlSignalsOnlyClause extends JmlSpecBodyClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------


    //@ requires nothing <==> exceptions == null;
    //@ requires exceptions != null ==> \nonnullelements(exceptions);
    public JmlSignalsOnlyClause( TokenReference where, 
                                 boolean isRedundantly,
                                 CClassType[] exceptions,
                                 boolean nothing ) {
	super( where, isRedundantly );
        this.exceptions = exceptions;
        this.nothing = nothing;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ int preferredOrder() {
	return PORDER_SIGNALS_CLAUSE;
    }

    //@ ensures \result == null <==> isNothing();
    //@ ensures \result != null ==> \nonnullelements(\result);
    public /*@ pure @*/ CClassType[] exceptions() {
	return exceptions;
    }

    public /*@ pure @*/ boolean isNothing() {
	return nothing;
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
        if (nothing) {
            return;  // nothing to check for \nothing
        }

        for (int i = 0; i < exceptions.length; i++) {
            // verity that the exception type is known?
            try {
                exceptions[i] = (CClassType)exceptions[i].checkType( context );
            }
            catch (UnpositionedError e) {
                // throw e.addPosition(getTokenReference());
                throw new PositionedError(getTokenReference(),
                                          JmlMessages.TYPE_UNKNOWN,
                                          exceptions[i]);
            }

            if (!exceptions[i].isAlwaysAssignableTo(CStdType.Throwable))
                check( context, false, JmlMessages.BAD_TYPE_IN_SIGNALS_ONLY,
                       exceptions[i].toVerboseString() );


            // verify that the exception is defined in the throw list, but
            // only checked exceptions need to be verified.
            if (exceptions[i].isCheckedException()) {
                CType ctype = CStdType.RuntimeException;
                //@ assert ctype != null;
                boolean declared =
                    // true if ctype is a subtype of RunTimeException ...
                    ctype.isAlwaysAssignableTo(exceptions[i])
                    // ... or is a supertype of RuntimeException
                    // i.e., (is Throwable or Exception).
                    || exceptions[i].isAlwaysAssignableTo(ctype);
                if (!declared) {
                    CClassType[] checked = context.getCMethod().throwables();
                    for (int j = 0; j < checked.length; j++) {
                        if (exceptions[i].isAlwaysAssignableTo(checked[j]) ||
                            checked[j].isAlwaysAssignableTo(exceptions[i])) {
                            declared = true;
                            break;
                        }
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
                            exceptions[i] );
         	    }
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
	    ((JmlVisitor)p).visitJmlSignalsOnlyClause(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    /** The exceptions listed, which will be null if \nothing is used. */
    private CClassType[] exceptions;

    /** True if no exceptions allowed. */
    private boolean nothing;

    //@ private invariant nothing <==> exceptions == null;
    //@ private invariant !nothing ==> \nonnullelements(exceptions);
    /*@ private invariant_redundantly exceptions != null
      @                                ==> \nonnullelements(exceptions);
      @*/
}
