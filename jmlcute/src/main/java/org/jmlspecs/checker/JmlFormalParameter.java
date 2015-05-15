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
 * $Id: JmlFormalParameter.java,v 1.11 2006/04/07 21:30:21 chalin Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * This class represents a formal parameter in a JML AST.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.11 $
 */

public class JmlFormalParameter extends JFormalParameter implements Constants {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    /**
     * Constructs a formal parameter node in the parsing tree.  
     * @param where		the line of this node in the source code
     * @param modifiers		modifiers applies to this parameter
     * @param desc		the sort of variable that this is, see
     *				constants in JLocalVariable
     * @param type		the static and dynamic types of this formal
     * @param ident		the name of this variable
     */
    public JmlFormalParameter( TokenReference where,
			       long modifiers,
			       int desc,
			       CSpecializedType type,
			       String ident) {
	super( where, modifiers, desc, type, ident );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    public CSpecializedType checkInterface( CContextType context ) throws PositionedError 
    {
	// System.err.println("\tparam.checkInterface:" + context.getClassContext().getHostClass());
	if(hasOtherFlags(modifiers, NULLITY_MODS | ACC_FINAL)) {
	    context.reportTrouble( 
		  new PositionedError( getTokenReference(),
				       JmlMessages.INVALID_PARAM_MODIFIER) );
	}
	if(hasFlag(modifiers(), ACC_NON_NULL) && hasFlag(modifiers(), ACC_NULLABLE)) {
	    context.reportTrouble( 
		  new PositionedError( getTokenReference(),
				       JmlMessages.NULLABLE_NON_NULL_TOGETHER ) );
	}
	checkNullityAdjustType(context);
	return super.checkInterface(context);
    }

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /** 
     * Ensures that at most one nullity modifier is used and that it
     * is applied to a reference type.  Also set the type of this
     * parameter to non-null if appropriate.
     */
    private void checkNullityAdjustType(CContextType context) throws PositionedError
    {
	// Check for proper use of nullity modifiers and adjust the type, if necessary.
	if( getType().isReference() ) {
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
		/* -----------------------------------------------------------------------------
		else {
		    String path = Utils.getFilePath(getTokenReference().file());
		    // specs/javax? or org/jmlspecs ...
		    // System.out.println("matches = " + path.matches(".*specs/.*") + "path = " + path);
		    if(!path.matches(".*specs/.*")) {
			check(context,
			      hasFlag(modifiers(), NULLITY_MODS),
			      JmlMessages.IMPLICIT_NULLITY);
		    }
		}
		----------------------------------------------------------------------------- */
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

    /** Returns any parameter modifiers as a String; if the String is
     * not empty, it will have a trailing space. 
     */
    public /*@ non_null @*/ String modifiersAsString() {
	return CTopLevel.getCompiler().modUtil().asString(modifiers());
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
	    ((JmlVisitor)p).visitJmlFormalParameter(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

}// JmlFormalParameter
