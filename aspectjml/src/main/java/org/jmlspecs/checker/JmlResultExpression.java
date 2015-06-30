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
 * $Id: JmlResultExpression.java,v 1.4 2002/09/06 22:36:24 cheon Exp $
 */

package org.jmlspecs.checker;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * JmlResultExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.4 $
 */

public class JmlResultExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlResultExpression( TokenReference where ) {
	super( where );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns the type of this result expression. This method method
     *  must be called after typechecking.
     */
    public CType getType() { return returnType; }

    /** Explicitly sets the type of this result expression. This method
     * can be used to build AST nodes by hands.
     */
    public void setType(CType type) {
        returnType = type;
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

	// is \result allowed in this context?
	if (!((JmlExpressionContext) context).resultOk())
	    context.reportTrouble(new PositionedError(getTokenReference(),
	       JmlMessages.RESULT_NOT_ALLOWED));

	returnType = context.getMethodContext().getCMethod().returnType();
	
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
		check( context, returnType != CStdType.Void, 
			       JmlMessages.RESULT_VOID );
	}
	
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
	    ((JmlVisitor)p).visitJmlResultExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private CType returnType;
}
