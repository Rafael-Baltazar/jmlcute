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
 * $Id: JmlRedundantSpec.java,v 1.5 2003/05/02 17:00:24 cruby Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/** 
 * A class representing JML redundant specifications. There are two kinds
 * of redundant specifications implications and examples. The production 
 * rule for redundant specifications, <tt>redundant-spec is defined as
 * follows.
 *
 * <pre>
 *  redundant-spec ::= implications [ examples ] 
 *    | examples
 *  implications ::= "implies_that" spec-case-seq
 *  examples ::= "for_example" example [ "also" example ] ...
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.5 $
 */

public class JmlRedundantSpec extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ private invariant implications != null || examples != null;
    public JmlRedundantSpec( TokenReference where,
			     JmlSpecCase[] implications,
			     JmlExample[] examples) {
	super( where );
	this.implications = implications;
	this.examples = examples;
    }
    
    public JmlRedundantSpec combine(JmlRedundantSpec second) {
	if (second == null) return this;
	JmlSpecCase[] implications 
	    = (JmlSpecCase[]) org.multijava.util.Utils
	    .combineArrays( implications(), second.implications());
	JmlExample[] examples 
	    = (JmlExample[]) org.multijava.util.Utils
	    .combineArrays( examples(), second.examples());
	return new JmlRedundantSpec(getTokenReference(),implications,examples);
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public JmlSpecCase[] implications() {
	return implications;
    }

    public JmlExample[] examples() {
	return examples;
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
     * Typechecks this <tt>redudant-spec</tt> in the context
     * in which it appears. Mutates the context to record the information 
     * learned during checking.
     *
     * @param context the context in which this appears
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError
    {
	if (implications != null)
	    for (int i = 0; i < implications.length; i++)
		implications[i].typecheck(context);

	if (examples != null)
	    for (int i = 0; i < examples.length; i++)
		examples[i].typecheck(context);
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
	    ((JmlVisitor)p).visitJmlRedundantSpec(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    //@ private invariant implications != null || examples != null;
    private JmlSpecCase implications[];
    private JmlExample examples[];

} // JmlRedundantSpec
