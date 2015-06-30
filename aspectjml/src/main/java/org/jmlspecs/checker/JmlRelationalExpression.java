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
 * $Id: JmlRelationalExpression.java,v 1.7 2005/08/25 23:46:30 chalin Exp $
 */

package org.jmlspecs.checker;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.mjc.*;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.mjc.JRelationalExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * This class represents the JML relational expressions.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.7 $
 */

public class JmlRelationalExpression extends JRelationalExpression
    implements Constants
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlRelationalExpression( TokenReference where, int oper,
				    JExpression left, JExpression right ) {
	super( where, oper, left, right );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ pure @*/ boolean isEquivalence()  {
	return oper == OPE_EQUIV;
    }

    public /*@ pure @*/ boolean isNonEquivalence()  {
	return oper == OPE_NOT_EQUIV;
    }

    public /*@ pure @*/ boolean isImplication() {
	return oper == OPE_IMPLIES;
    }

    public /*@ pure @*/ boolean isBackwardImplication() {
	return oper == OPE_BACKWARD_IMPLIES;
    }

    public /*@ pure @*/ CType getType() {
	return CStdType.Boolean;
    }

    public /*@ pure @*/ boolean isSubtypeOf() {
	return oper == OPE_SUBTYPE;
    }
	
    public /*@ pure @*/ int oper() {
	return oper;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    public /*@ pure @*/ String opString() {
	String op;
	switch (oper) {
	case OPE_EQUIV:
	    op = "<==>";
	    break;
	    
	case OPE_NOT_EQUIV:
	    op = "<=!=>";
	    break;
	    
	case OPE_IMPLIES:
	    op = "==>";
	    break;

	case OPE_BACKWARD_IMPLIES:
	    op = "<==";
	    break;
	    
	case OPE_SUBTYPE:
	    op = "<:";
	    break;
	    
	default:
	    op = super.opString();
	    break;
	} // end of switch (oper)
	return op;
    }
	
    public /*@ pure @*/ String toString() {
	return left.toString() + " " + opString() + " " + right.toString();
    }

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
	left = left.typecheck(context);
	right = right.typecheck(context);

	if (isSubtypeOf()) {
	    check( context, 
		   left.getType().equals(CStdType.Class) 
		   && right.getType().equals(CStdType.Class),
		   JmlMessages.SUBTYPE_OF_TYPE,
		   left.getType().toVerboseString(), // WMD
		   right.getType().toVerboseString()); // WMD

	} else if (( oper() == OPE_LT || oper() == OPE_LE )
		&& left.getType().isReference()
		&& right.getType().isReference() ) {

		// Comparison of lock order

	} else if (oper() == OPE_EQUIV || oper() == OPE_NOT_EQUIV ||
		   oper() == OPE_IMPLIES || oper() == OPE_BACKWARD_IMPLIES) {
		
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
			check( context, 
					left.getType() == CStdType.Boolean
					&& right.getType() == CStdType.Boolean,
					JmlMessages.EQUIVALENCE_TYPE,
					left.getType().toVerboseString(), // WMD
					right.getType().toVerboseString()); // WMD
		}
	} else {
	    // Be careful - don't typecheck the arguments twice!
	    return super.typecheck_helper(context);
	}

	type = CStdType.Boolean;

	// !FIXME! perform static optimization (see JConditionalAndExp.)
	// or maybe leave it to the RAC (e.g., for eval of quantifiers)

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
	    ((JmlVisitor)p).visitJmlRelationalExpression( this );
	else
	    throw new UnsupportedOperationException( JmlNode.MJCVISIT_MESSAGE );
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

} // JmlRelationalExpression
