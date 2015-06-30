/*
 * Copyright (C) 2002 Iowa State University
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
 * $Id: JmlModifier.java,v 1.5 2005/04/26 02:40:26 kui_dai Exp $
 */

package org.jmlspecs.ajmlrac;

import org.multijava.mjc.CModifier;

import java.util.ArrayList;

/**
 * A class providing utilities for operating on modifier bit masks. 
 * JML-specific modifiers such as <code>non_null</code> can be returned
 * in string forms either with or without the JML annotation markers,
 * e.g., <code>non_null</code> or 
 * <code>&#047;&#042;@ non_null @&#042;&#047;</code>, by setting a flag
 * using the method <code>setWithoutMarkers</code>.
 *
 * @see RacPrettyPrinter
 */
public class JmlModifier extends CModifier
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /**
     * Instantiate the modifier utilities for the default modifier 
     * bit-masks and names. 
     */
    public JmlModifier() {
	this(RacConstants.ACCESS_FLAG_ARRAY, RacConstants.ACCESS_FLAG_NAMES);
    }
    
    /**
     * Instantiate the modifier utilities for the given modifier 
     * bit-masks and names.
     *
     * @param codes an array of modifier bit-masks, typically from the
     *			<code>ACCESS_FLAG_ARRAY</code> field of the 
     *			appropriate <code>Constants</code> interface.
     * @param names an array of modifier names, typically from the
     *			<code>ACCESS_FLAG_NAMES</code> field of the 
     *			appropriate <code>Constants</code> interface.
     *
     * @see org.multijava.util.classfile.Constants
     * @see org.multijava.util.classfile.Constants#ACCESS_FLAG_ARRAY
     * @see org.multijava.util.classfile.Constants#ACCESS_FLAG_NAMES
     */
    public JmlModifier( long[] codes, String[] names ) {
	super(codes, names);
    }
    
    //---------------------------------------------------------------------
    // OPERATORS
    //---------------------------------------------------------------------

    /**
     * Returns an array of the names of all the modifiers in the
     * preferred order. */
    public String[] asStrings(long modifiers) {
	ArrayList results = new ArrayList(codes.length);
	for (int i = 0; i < codes.length; i++) {
	    if (hasFlag(modifiers, codes[i]) && names[i].length() > 0) {
		if (isJmlModifier(codes[i]) && !withoutMarkers)
		    results.add( "/*@ " + names[i] + " @*/");
		else
		    results.add( names[i] );
	    }
	}
	String[] resultArr = new String[ results.size() ];
	results.toArray( resultArr );
	
	return resultArr;
    }

    /**
     * Returns <code>true</code> if JML modifiers such as <code>non_null</code>
     * are returned by the methods like  <code>asString</code> without
     * the JML annotation markers, e.g., <code>non_null</code> instead of
     * <code>&#047;&#042;@ non_null @&#042;&#047;</code>;
     * otherwise, return <code>false</code>.
     *
     * @see #setWithoutMarkers(boolean)
     */
    public /*@ pure @*/ boolean withoutMarkers() {
	return withoutMarkers;
    }

    /**
     * Set whether the methods like <code>asString</code> should return
     * JML modifier strings without JML annotation markers, e.g., 
     * <code>non_null</code> instead of
     * <code>&#047;&#042;@ non_null @&#042;&#047;</code>.
     * 
     * @see #withoutMarkers()
     */
    public void setWithoutMarkers(boolean flag) {
	withoutMarkers = flag;
    }

    /** Returns <code>true</code> if arguments are JML modifiers. */
    protected boolean isJmlModifier(long modifiers) {
	// 16 low-order bits (last 4 hex digits) are used for VM flags
	return (modifiers & 0xFFFFFFFFFFFF0000L) != 0;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /**
     * Indicates whether the methods like <code>asString</code> should return
     * JML modifier strings without JML annotation markers, e.g., 
     * <code>non_null</code> instead of normal 
     * <code>&#047;&#042;@ non_null @&#042;&#047;</code>.
     */
    private boolean withoutMarkers = false;
}
