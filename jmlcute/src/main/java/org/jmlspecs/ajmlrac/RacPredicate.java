/*
 * Copyright (C) 2001 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: RacPredicate.java,v 1.3 2003/02/02 01:26:58 davidcok Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlSpecExpression;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.MjcVisitor;

/**
 * An AST node class for RAC-specific predicates. This class is a 
 * refinement of the class <code>JmlPredicate</code> and is treated
 * specially by the transformation classes such as
 * <code>TransPredicate</code>. If the predicate does not hold, for
 * example, its token reference is processed and stored for error
 * message composition.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */
public class RacPredicate extends JmlPredicate {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public RacPredicate( JmlSpecExpression specExpression ) {
	super(specExpression);
    }

    public RacPredicate( JmlPredicate predicate ) {
	this(predicate.specExpression());
    }

    /** 
     * Constructs a new RAC predicate with the given expression.
     */
    public RacPredicate( /*@ non_null @*/ JExpression expression ) {
	this(expression, null);
    }
    
    /** 
     * Constructs a new RAC predicate with the given expression and
     * associated message. 
     */
    public RacPredicate( /*@ non_null @*/ JExpression expression, 
                         String message ) {
	this(new JmlSpecExpression(expression));
        this.message = message;
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------
    
    /** Returns the message associated with this RAC predicate. The
     * returned value may be null. 
     *
     * <pre><jml>
     * ensures \result == message;
     * </jml></pre>
     */
    public String message() {
        return message;
    }

    /** Returns true if this RAC predicate has an associated message.
     *
     * <pre><jml>
     * ensures \result == (message != null);
     * </jml></pre>
     */
    public boolean hasMessage() {
        return message != null;
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof RacVisitor)
	    ((RacVisitor)p).visitRacPredicate( this );
	else
	    throw new UnsupportedOperationException("Not RacVisitor!");
    }

    /** Returns true if this predicate is a true literal. */
    public boolean isTrueLiteral() {
	JExpression e = specExpression().expression();
	return (e instanceof JBooleanLiteral && ((JBooleanLiteral)e).booleanValue());
    }


    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------
    
    /**
     * Message associated with this RAC predicate. It can be null.
     */
    private /*@ spec_public @*/ String message;
    
    public boolean countCoverage = false;
    
    public void countCoverage() { countCoverage = true; }
}
