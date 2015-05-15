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
 * $Id: JmlMethodName.java,v 1.13 2006/06/19 01:29:58 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodNotFoundError;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JExplicitConstructorInvocation;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.mjc.JRealLiteral;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JTypeNameExpression;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This AST node represents a method name in a JML annotation.
 * The syntax for the method name is defined as follows.
 *
 * <pre>
 *  method-name ::= method-ref [ "(" [ param-disambig-list ] ")" ]
 *  method-ref ::= method-ref-start [ "." ident ] ...
 *    | "new" reference-type
 *  method-ref-start := "super" | "this" | ident | "\other"
 *  param-disambig-list ::= param-disambig [ "," param-disambig ] ...
 *  param-disambig ::= type-spec [ ident [ dims ]]
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.13 $
 */

public class JmlMethodName extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires subnames != null;
    public JmlMethodName( TokenReference where, JmlName[] subnames,
			  CType[] paramDisambigList ) {
	super( where );
	this.subnames = subnames;
	this.paramDisambigList = paramDisambigList;
    }

    protected JmlMethodName( TokenReference where, 
			     CType[] paramDisambigList ) {
	super( where );
	this.subnames = null;
	this.paramDisambigList = paramDisambigList;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the subname part of this method name. */
    public /*@ non_null @*/ JmlName[] subnames() {
	return subnames == null ? new JmlName[0] : subnames;
    }

    public CType[] paramDisambigList() {
	return paramDisambigList;
    }

    /** Indicates if this method name has a list of parameter types
     * specified. The return value of false means that the method name
     * has no such parameter types specified (e.g., m1). The return
     * value of true means that the method has parameter types specified
     * including empty ones (e.g., m1(), m1(int x), etc.).
     */
    public boolean hasParamDisambigList() {
	return paramDisambigList != null;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@non_null@*/ String toString()  {
	if (stringRepresentation == null) {
	    if (subnames != null) {
		StringBuffer result = new StringBuffer( "" );
		for (int i = 0; i < subnames.length; i++) {
		    if (i>0) {
			result.append( "." );
		    }
		    result.append( subnames[i].getName() );
		}
		CType[] pl = paramDisambigList;
		if (pl != null) {
		    result.append("(");
		    for (int i=0; i<pl.length; ++i) {
			if (i != 0) result.append(",");
			result.append(pl[i].toString()); 
		    }
		    result.append(")");
		}
		stringRepresentation = result.toString();
	    } else {
		stringRepresentation = "";
	    }
	}
	return stringRepresentation;
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    protected CMethod lookupMethod( CType[] argTypes, 
				    CExpressionContextType context ) 
	throws UnpositionedError, PositionedError
    {
	String ident = methodName.getName();
	CMethodSet results;
	CClass receiver = null;
	if (prefix != null) {
	    receiver = prefix.getType().getCClass();
	    CClassType[] sub = prefix.getType().isGenericType()
		? prefix.getType().getArguments()
		: CClassType.EMPTY;
	    results = receiver.lookupMethodOrSet(ident, argTypes, sub, context);
	} else {
	    results = context.lookupMethodOrSet( ident, argTypes );
	}
	
	CMethod result = (results == null) ? null : results.getFirst();

	if( result == null ) {

	    throw new CMethodNotFoundError( methodName.getTokenReference(), 
					    getPrefixName() + ident,
					    argTypes,
					    false );
	}
	return result;
    }
    /**
     * Returns a String representation of the prefix to the method, 
     * i.e., the receiver expression, used for creating error messages.
     */
    public String getPrefixName() {
	String prefixName;

	if( prefix instanceof JNameExpression ) {
	    prefixName = 
		((JNameExpression) prefix).qualifiedName() + ".";
	} else if( prefix instanceof JTypeNameExpression ) {
	    prefixName =  
		((JTypeNameExpression) prefix).qualifiedName() + ".";
	} else if (prefix != null) {
	    prefixName = prefix.getType().toString() + ".";
	} else {
	    prefixName = "";
	}
	return prefixName;
    }

    /**
     * Typechecks this method name in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking. This method also perform both visibility check
     * and purity check; however, the purity check is performed only
     * if the argument <code>checkPurity</code> is true.
     *
     * @param context the context in which this appears
     * @param privacy the visibility level with which to typecheck
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context, long privacy,
                           boolean checkPurity ) 
	throws PositionedError
    {
	TokenReference where  = getTokenReference();
	args = new JExpression[ 
	   paramDisambigList == null ? 0 :  paramDisambigList.length]; 

	// first, check parameter types and build args for later use
	if (paramDisambigList != null) {
	    for (int i = 0; i < paramDisambigList.length; i++) {
		try {
		    paramDisambigList[i] =
			paramDisambigList[i].checkType( context );
		    args[i] = defaultValue( paramDisambigList[i] );
		}
		catch (UnpositionedError e) {
		    context.reportTrouble(
		    	new PositionedError(getTokenReference(),
				JmlMessages.TYPE_UNKNOWN, paramDisambigList[i])
			);
		}
	    }
	}

	if ( subnames != null ) {
	    if (subnames[0].isWildcard()) {
		    throw new PositionedError(
				  subnames[0].getTokenReference(), 
				  JmlMessages.MISPLACED_DOT_STAR );
	    } else {
	    // we check the validity of constructors indirectly by
            // building and typechecking its constructor invocation
            // with arguments consisting of default values. 

            buildPrefix();
	    if ( methodName.isWildcard() ) {
		if (subnames.length > 2) {
		    throw new PositionedError(
				  methodName.getTokenReference(), 
				  JmlMessages.MISPLACED_DOT_STAR );
		}
		// nothing more to do
		return;
	    }

	    String ident = methodName.getName();
	    JmlExpressionContext ectx
		= JmlExpressionContext.createPrecondition( context );
	    try {
		if ( methodName.isThis() || methodName.isSuper() ) {
		    if ( !context.isInConstructor() ) {
			throw new PositionedError(
				  methodName.getTokenReference(), 
				  MjcMessages.CONSTRUCTOR_ILLEGAL_EXPLICIT );
		    }
		    JExpression exp 
			= new JExplicitConstructorInvocation( 
					 methodName.getTokenReference(),
					 prefix, 
					 ident, 
					 args); 
		    exp = exp.typecheck( ectx );
		    prefix = ((JExplicitConstructorInvocation)exp).prefix();
		    method = ((JExplicitConstructorInvocation)exp).method();
		} else {
		    if (prefix != null) {
			prefix = prefix.typecheck( ectx );
		    }
		    if (paramDisambigList == null) {
			CClass receiver;
			CMethodSet results = null;
			if (prefix != null) {
			    receiver = prefix.getType().getCClass();
			} else {
			    receiver = context.getClassContext().getHostClass();
			}
			results = ((JmlSourceClass)receiver)
			    .lookupJMLMethodName(ident, context);
			if (results != null && results.size() > 1) {
			    throw new PositionedError(
				  methodName.getTokenReference(), 
				  JmlMessages.AMBIGUOUS_CALLABLE_METHOD,
				  getPrefixName() + ident );
			}
			if ( results == null || results.size() == 0 ) {
			    throw new CMethodNotFoundError( 
					methodName.getTokenReference(),
					getPrefixName() + ident,
					paramDisambigList,
					false );
			}
			method = results.getFirst();
		    } else {
			method = lookupMethod( paramDisambigList, ectx );
		    }
		}

		// check visibility
		if ( method != null ) {
		    if ( !JmlExpressionChecker
			 .isVisibilityOk(privacy, method.modifiers()) ) {

			context.reportTrouble(new PositionedError(
				  methodName.getTokenReference(), 
				  JmlMessages.METHOD2_VISIBILITY,
				  new Object[] {
				      ident, 
				      JmlNode.privacyString(method.modifiers()),
				      JmlNode.privacyString(privacy)
				  } ) );
		    }
		    checkForExactArgumentTypes(context);
		}
	    } catch ( PositionedError e ) {
		context.reportTrouble(e);
	    } catch ( UnpositionedError e ) {
		context.reportTrouble(new PositionedError(
					   methodName.getTokenReference(), 
					   e.getFormattedMessage() )
					  );
	    }
	    }

	}
    }
    private void checkForExactArgumentTypes(CFlowControlContextType context) {
	// make sure the parameter types match exactly
	CSpecializedType[] parameters = method.parameters();
	if (paramDisambigList != null) {
	    int s = 0;
	    if (parameters.length == paramDisambigList.length+1) {
		// There is an extra argument in constructors of 
		// non-static nested inner classes
		s = 1;
	    } else if (parameters.length != paramDisambigList.length) {
		// should not happen since the method or constructor 
		// has already been resolved.  
		// Here we are now making sure the parameters match exactly
		throw new RuntimeException("Reached unreachable!");
	    }
	    for (int i = s; i < parameters.length; i++) {
		if (!parameters[i].staticType().equals(paramDisambigList[i-s]))
		{
		    context.reportTrouble(
		        new CMethodNotFoundError( 
				methodName.getTokenReference(),
				getPrefixName() + methodName.getName(),
				paramDisambigList,
				false ));
		}
		break;
	    }
	}
    }

    /** Return the default value for type; used for typechecking. */
    private JExpression defaultValue( CType type ) {
	JExpression val = null;
	if (type.isReference()) {
	    val = new JNullLiteral(getTokenReference());
	} else if (type == CStdType.Boolean) {
	    val = new JBooleanLiteral(getTokenReference(), false);
	} else if (type.isOrdinal()) {
	    val = new JOrdinalLiteral(getTokenReference(), "0");
	} else {
	    val = new JRealLiteral(getTokenReference(), "0");
	}
	
	return new JCastExpression(getTokenReference(), val, type);
    }

    /** Compose the subnames into a prefix expression separated from the 
     *  method name for typechecking purposes.
     */
    private void buildPrefix()
    {
	prefix = null;
	// first build the prefix
	for (int i = 0; i < subnames.length-1; i++) {
	    //@ assert (* subnames[i] is ident, this, or super *);
	    TokenReference where = subnames[i].getTokenReference();
	    if (subnames[i].isIdent()) {
		prefix = new JNameExpression(where, prefix, 
					     subnames[i].ident());
	    } else if (subnames[i].isThis()) {
		prefix = new JThisExpression(where, prefix);
	    } else if (subnames[i].isSuper()) {
		// super is guranteed to be the first by the parser
		prefix = new JSuperExpression(where);
	    } else {
		throw new RuntimeException("Reached unreachable!");
	    }
	}
	methodName = subnames[subnames.length-1];
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
	    ((JmlVisitor)p).visitJmlMethodName(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ invariant subnames == null <==> this instanceof JmlConstructorName;

    /**
     * The name of the method as given in the source code.
     */
    protected JmlName[] subnames;

    protected JExpression prefix;
    protected JmlName methodName;

    /**
     * An array of the parameter types, used to disambiguate between
     * overloaded methods.  May be null.  */
    protected CType[] paramDisambigList;

    /** Internally used for typechecking */
    protected JExpression args[]; 

    /** Internally used */
    protected String stringRepresentation = null;  //@ in objectState;

    /**
     * The method call specified, as determined by the
     * static receiver and argument types.  
     */
    protected CMethod method;

}// JmlMethodName
