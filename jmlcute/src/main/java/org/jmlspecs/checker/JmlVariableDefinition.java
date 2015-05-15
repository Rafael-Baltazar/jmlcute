/* $Id: JmlVariableDefinition.java,v 1.5 2006/02/11 03:06:40 chalin Exp $
 *
 * Copyright (C) 2000-2006 Iowa State University
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
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * A wrapper of the class JVariableDefinition to store JML-specific
 * information.  Although JVariableDefinition is documented as holding
 * local variables, this class is also used to hold bound variables
 * (such as those appearing in quantified expressions.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlVariableDefinition extends JVariableDefinition implements Constants {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Construct a node in the parsing tree.  This method is directly
     * called by the parser.  */
    public JmlVariableDefinition( TokenReference where,
                                  long modifiers,
                                  CType type,
                                  String ident,
                                  JExpression initializer ) {
	super( where, modifiers, type, ident, initializer );
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Returns true if this variable have a RAC field generated for
     * it. */
    public boolean hasRacField() {
	return racField != null;
    }

    /** Set the name of RAC field of this variable to the given one. */
    public void setRacField(String name) {
	racField = name;
    }

    /** Returns the name of RAC field generated for this variable. The
     * return value may be null. */
    public String racField() {
        return racField;
    }

    //---------------------------------------------------------------------
    // Visitor
    //---------------------------------------------------------------------

    public void accept( MjcVisitor m) {
        ((JmlVisitor)m).visitJmlVariableDefinition(this);
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
     * Typechecks the statement and mutates the context to record
     * information gathered during typechecking.
     *
     * @param context the context in which this expression appears
     * @exception PositionedError if the check fails */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError 
    {
	try {
	    JmlNode.enterSpecScope( modifiers() );
	    super.typecheck(context);
	    checkNullityAdjustType(context);
	}
	finally{
	    JmlNode.exitSpecScope( modifiers() );
	}
    }

    /** 
     * Ensures that at most one nullity modifier is used and that it
     * is applied to a reference type.  Also set the type of this
     * variable to non-null if appropriate.
     */
    private void checkNullityAdjustType(CContextType context) throws PositionedError
    {
	// Check for proper use of nullity modifiers and adjust the type, if necessary.
	if( getType().isReference() ) {
	    // Will this have been checked?  How about other modifiers?
	    check(context, 
		  !(hasFlag(modifiers(), ACC_NON_NULL) && hasFlag(modifiers(), ACC_NULLABLE)),
		  JmlMessages.NULLABLE_NON_NULL_TOGETHER);

	    // getType().isReference() ==> getType() instanceof CClassType
	    CClassType type = (CClassType) getType();

	    // Set nullity qualifier of the type of this, if necessary.
	    if(hasFlag(modifiers(), ACC_NON_NULL)) {
		setNonNull();
	    } else if(!hasFlag(modifiers(), ACC_NULLABLE)) {
		// No explicit nullity modifier is present
		CClass clazz = context.getClassContext().getHostClass();
		if(Main.jmlOptions == null) {
		    throw new IllegalStateException("Main.jmlOptions should not be null");
		}
		if(hasFlag(clazz.access().modifiers(), ACC_NON_NULL_BY_DEFAULT)
		   || !hasFlag(clazz.access().modifiers(), ACC_NULLABLE_BY_DEFAULT)
		   && Main.jmlOptions.defaultNonNull()) {
		    setNonNull();
		}
	    }
	} else {
	    // There should be no nullity modifiers.
	    check(context, 
		  !hasFlag(modifiers(), NULLITY_MODS),
		  JmlMessages.NULLITY_MODIFIERS_FOR_NON_REF_TYPE,
		  new Object[] { CTopLevel.getCompiler().modUtil()
				 .asString(modifiers() & NULLITY_MODS).trim(), 
				 getType() });
	}
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    
    /**
     * The name of RAC field generated for this variable.
     */
    private String racField;
}
