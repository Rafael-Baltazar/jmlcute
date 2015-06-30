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
 * $Id: JmlExtendingSpecification.java,v 1.7 2003/09/30 10:47:34 davidcok Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;

/** 
 * A method specification that extetends inherited specifications.  In
 * JML, one form of extensions is supported: "also" extension. The
 * production rule for specification extension,
 * <tt>extending-specification</tt> is defined as follows.
 *
 * <pre>
 *  extending-specification ::= "also" specification
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.7 $ */

public class JmlExtendingSpecification extends JmlSpecification {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    protected JmlExtendingSpecification( TokenReference where, 
				JmlSpecCase[] specCases,
				JmlRedundantSpec redundantSpec) 
    {
	super( where, specCases, redundantSpec );
    }
    
    /** Construct an instance of JmlExtendingSpecification that represents
     * an OR extension.
     */    
    public JmlExtendingSpecification( JmlSpecification s ) {
	this(s.getTokenReference(), s.specCases(), s.redundantSpec());
    }
    
    public JmlSpecification newInstance(
				 JmlSpecCase[] specCases,
				 JmlRedundantSpec redundantSpec)
    {
	return new JmlExtendingSpecification(
			     getTokenReference(), specCases, 
			     redundantSpec);
    }
 
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // VISITOR
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlExtendingSpecification( this );
	else
	    super.accept( p );
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

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

} // JmlExtendingSpecification
