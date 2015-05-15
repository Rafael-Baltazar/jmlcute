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
 * $Id: JmlConstructorName.java,v 1.7 2005/09/12 19:02:00 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClassType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This AST node represents a constructor in a JML annotation.
 * The syntax for the method name is defined as follows.
 *
 * <pre>
 *  method-name ::= method-ref [ "(" [ param-disambig-list ] ")" ]
 *  method-ref ::= "new" reference-type | ...
 *  param-disambig-list ::= param-disambig [ "," param-disambig ] ...
 *  param-disambig ::= type-spec [ ident [ dims ]]
 * </pre>
 *
 *
 * @author Curtis Clifton
 * @version $Revision: 1.7 $
 */

public class JmlConstructorName extends JmlMethodName {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlConstructorName( TokenReference where, CType ownerType,
			       CType[] paramDisambigList ) {
	super( where, paramDisambigList );
	this.ownerType = ownerType;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public CType type() {
	return ownerType;
    }
	
    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public CType ownerType() {
	return ownerType;
    }

    public /*@non_null@*/ String toString()  {
	if (stringRepresentation == null) {
	    StringBuffer result = new StringBuffer( ownerType.toString() );
	    
	    CType[] pl = paramDisambigList();
	    if (pl != null) {
		result.append("(");
		for (int i=0; i<pl.length; ++i) {
		    if (i != 0) result.append(",");
		    result.append(pl[i].toString()); 
		}
		result.append(")");
	    }
	    stringRepresentation = result.toString();
	}
	return stringRepresentation;
    }

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks this constructor name in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking. This method also perform both visibility check
     * and purity check; however, the purity check is performed only
     * if the argument <code>checkPurity</code> is true.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context, long privacy,
                           boolean checkPurity ) 
	throws PositionedError
    {
	super.typecheck( context, privacy, checkPurity );
	
	check( context, 
	       ownerType.isReference() && !ownerType.isArrayType(), 
	       JmlMessages.NOT_NON_ARRAY_REFERENCE_TYPE_IN_METHOD_NAME, 
	       ownerType.toVerboseString() ); // WMD

	// we check the validity of constructor name by building and
	// typechecking a "new" expression with arguments consisting of
	// default values.
	JExpression expr = new JNewObjectExpression(
	    getTokenReference(), (CClassType) ownerType, null, args );
	JmlExpressionContext ectx
	    = JmlExpressionContext.createPrecondition( context );
	expr = expr.typecheck( ectx );

        // visibility check
        JmlExpressionChecker.perform(ectx, privacy, expr, checkPurity);
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
	    ((JmlVisitor)p).visitJmlConstructorName(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    protected CType ownerType;

}// JmlConstructorName
