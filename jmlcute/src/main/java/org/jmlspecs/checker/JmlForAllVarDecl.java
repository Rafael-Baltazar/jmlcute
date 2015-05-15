/*
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
 *
 * $Id: JmlForAllVarDecl.java,v 1.7 2006/02/02 16:42:21 chalin Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.UnpositionedError;

/**
 * An AST node class for the JML forall variable declarations.
 * The syntax for defining forall variables is as follows.
 *
 * <pre>
 *  forall-var-decls ::= forall-var-decl [ forall-var-decl ] ...
 *  forall-var-decl ::= "forall" [ bound-var-modifiers ] quantified-var-decl ";"
 *  quantified-var-decl ::= type-spec quantified-var-declarator
 *      [ "," quantified-var-declarator ] ...
 *  quantified-var-declarator ::= ident [ dims ]
 *  bound-var-modifier ::= "non_null" | "nullable"
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.7 $
 */

public class JmlForAllVarDecl extends JmlSpecVarDecl {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlForAllVarDecl( TokenReference where, 
			     JVariableDefinition[] quantifiedVarDecls ) {
	super( where );
	this.quantifiedVarDecls = quantifiedVarDecls;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JVariableDefinition[] quantifiedVarDecls() {
	return quantifiedVarDecls;
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
     * Typechecks the specification variable declarations in the context 
     * in which it appears. Mutates the context to record the information
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context, long privacy )
	throws PositionedError
    {
	for (int i = 0; i <  quantifiedVarDecls.length; i++) {
	    JVariableDefinition var =  quantifiedVarDecls[i];
	    try {
		context.addVariable(var);
		var.typecheck(context); 

		// assume it is initialized
		// INTENT: to prevent from issuing uninit. var ref errors
		context.initializeVariable(var);
	    } catch( UnpositionedError e ) {
		throw e.addPosition( var.getTokenReference() );
	    }
	}
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
	    ((JmlVisitor)p).visitJmlForAllVarDecl(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JVariableDefinition[] quantifiedVarDecls;

}
