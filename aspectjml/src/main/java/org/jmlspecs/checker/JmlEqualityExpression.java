/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
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
 * $Id: JmlEqualityExpression.java,v 1.4 2002/11/03 03:03:27 davidcok Exp $
 */

// FIXME - Don't think we need this class at all now that JmlSTdType.TYPE is equal to CStdType.Class.  DRCok

package org.jmlspecs.checker;

import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;
/**
 * This class represents the AST node for the equality operators.
 * These are <code>==</code> and <code>!=</code> (JLS2 15.21). */
public class JmlEqualityExpression extends JEqualityExpression {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a node in the parsing tree.
     * This method is directly called by the parser.
     * @param	where		the line of this node in the source code
     * @param	oper		the operator
     * @param	left		the left operand
     * @param	right		the right operand
     */
    public JmlEqualityExpression( TokenReference where,
				int oper,
				JExpression left,
				JExpression right )
    {
	super( where, oper, left, right );
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Accepts the specified visitor
     * @param	p		the visitor
     */
    public void accept(MjcVisitor p) {
	p.visitEqualityExpression( this );
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // ----------------------------------------------------------------------

}

