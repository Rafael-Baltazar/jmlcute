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
 * $Id: JmlFreshExpression.java,v 1.3 2002/09/21 21:43:06 cheon Exp $
 */

package org.jmlspecs.checker;
import java.util.Iterator;
import java.util.List;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * JmlFreshExpression.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.3 $
 */

public class JmlFreshExpression extends JmlExpression {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlFreshExpression( TokenReference where,
			       JmlSpecExpression[] specExpressionList ) {
	super( where );
	this.specExpressionList = specExpressionList;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ JmlSpecExpression[] specExpressionList() {
	return specExpressionList;
    }

    public /*@ pure @*/ CType getType() {
	return CStdType.Boolean;
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

	// is \fresh allowed in this context?
	if (!((JmlExpressionContext) context).freshOk())
	    context.reportTrouble(new PositionedError(getTokenReference(),
	       JmlMessages.FRESH_NOT_ALLOWED));
	
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
		for (int i = 0; i < specExpressionList.length; i++) {
		    //@ assert specExpressionList[i] != null;
		    specExpressionList[i] = (JmlSpecExpression)
			specExpressionList[i].typecheck(context);
		    final CType type = specExpressionList[i].getType();
		    check(context, type.isReference(), JmlMessages.TYPE_IN_FRESH, 
			  type);
		}
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
	    ((JmlVisitor)p).visitJmlFreshExpression(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JmlSpecExpression[] specExpressionList;

}
