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
 * $Id: JmlLetVarDecl.java,v 1.6 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * An AST node class for the JML let (old) variable declarations.
 * The syntax for defining let variables is as follows.
 *
 * <pre>
 *  let-var-decls ::= local-spec-var-decl [ local-spec-var-decl ] ...
 *  local-spec-var-decl ::= type-spec spec-variable-declarators ";"
 * </pre>
 *
 * @author Curtis Clifton
 * @version $Revision: 1.6 $
 */

public class JmlLetVarDecl extends JmlSpecVarDecl {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlLetVarDecl( TokenReference where, 
			  JVariableDefinition[] specVariableDeclarators )
    {
	super( where );
	this.specVariableDeclarators = specVariableDeclarators;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JVariableDefinition[] specVariableDeclarators() {
	return specVariableDeclarators;
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
	for (int i = 0; i < specVariableDeclarators.length; i++) {
	    JVariableDefinition var = specVariableDeclarators[i];
	    try {
		context.addVariable(var);
		var.typecheck(context);
		// error if old var is unitialized
		check(context, 
		      var.hasInitializer(),
		      JmlMessages.UNINITIALIZED_OLD_VAR,
		      var.ident());
		// check visibility and purity of the initializer
        if (var.hasInitializer()) {
			JmlExpressionChecker.perform(context, privacy, var.expr());
		}
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
	    ((JmlVisitor)p).visitJmlLetVarDecl(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JVariableDefinition[] specVariableDeclarators;
}
