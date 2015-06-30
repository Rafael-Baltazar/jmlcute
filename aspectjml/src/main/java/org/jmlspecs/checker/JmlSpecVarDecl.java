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
 * $Id: JmlSpecVarDecl.java,v 1.4 2005/04/26 02:40:17 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * An abstraction of JML specification variable declarations. JML supports
 * two kinds of specification variables: let (old) variables and forall
 * variables. This abstract class is the common superclass of them.
 * The syntax for JML specification variable declarations is as follows.
 *
 * <pre>
 *  spec-var-decls ::= forall-var-decls [ let-var-decls ]
 *    | let-var-decls
 * </pre>
 * 
 * For the definitions of production rules <tt>forall-var-decls</tt> and
 * <tt>let-var-decls</tt>, refer to classes <tt>JmlForAllVarDecl</tt> and
 * <tt>JmlLetVarDecl</tt> respectively.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.4 $
 */

public abstract class JmlSpecVarDecl extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlSpecVarDecl( TokenReference where ) {
	super( where );
	racGenerated = false;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /** Is RAC code generated for this spec variable? */
    public boolean racGenerated() {
	return racGenerated;
    }

    /** Indicate that RAC code has been generated for this node */
    public void setRacGenerated() {
	racGenerated = true;
    }

    //---------------------------------------------------------------------
    // Visitor
    //---------------------------------------------------------------------

	public void accept( MjcVisitor m) {
		((JmlVisitor)m).visitJmlSpecVarDecl(this);
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
    public abstract void typecheck(CFlowControlContextType context, 
                                   long privacy)
	throws PositionedError;

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /** Indicate whether RAC code be generated for this spec var */
    private boolean racGenerated;
}
