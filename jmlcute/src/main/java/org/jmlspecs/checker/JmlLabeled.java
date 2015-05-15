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
 * $Id: JmlLabeled.java,v 1.2 2002/03/15 21:43:17 cclifton Exp $
 */

package org.jmlspecs.checker;
import org.multijava.util.compiler.TokenReference;

/**
 * JmlLabeledClause.java
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.2 $
 */

/**
 * This abstract class represents a specfication statement clause that can 
 * have a label (e.g., JmlBreaksClause and JmlContinuesClause).
 */
public abstract class JmlLabeled extends JmlSpecStatementClause {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires predOrNot != null ==> !isNotSpecified;
    //@ requires isNotSpecified ==> predOrNot == null;
    protected JmlLabeled( TokenReference where,
			  boolean isRedundantly,
			  String label,
			  JmlPredicate predOrNot,
			  boolean isNotSpecified) {
	super( where, isRedundantly, predOrNot, isNotSpecified );
	this.label = label;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public String label() {
	return label;
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

    private String label;

}
