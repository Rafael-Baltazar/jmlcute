/*
 * Copyright (C) 2003 Iowa State University.
 *
 * This file is part of jml, the Java Modeling Language Checker.
 *
 * based in part on work:
 *
 * Copyright (C) 2000-2001 Iowa State University
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
 * $Id: JmlNumericType.java,v 1.15 2004/06/20 02:20:36 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.FastStringBuffer;

/**
 * This class represents the JML primitive numeric types bigint and real.
 * @see	CNumericType
 */
public class JmlNumericType extends CNumericType implements Constants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructor
     * @param	typeID		the ident (int value) of this type
     */
    //@ requires super.isValidNumericTypeID(typeID);
    //@ modifies this.*;
    protected JmlNumericType(int typeID) {
	super(typeID);
    }

    /*@ also
      @ protected normal_behavior
      @   assignable \nothing;
      @   ensures \result <== super.isValidNumericTypeID(typeID)
      @     ||  typeID == TID_BIGINT
      @     ||  typeID == TID_REAL;
      @*/
    protected /*@ pure @*/ boolean isValidNumericTypeID(int typeID) {
	return super.isValidNumericTypeID(typeID) ||
	    typeID == TID_BIGINT ||
	    typeID == TID_REAL;
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Transforms this type to a string
     */
    //@ also
    //@ assignable objectState, System.out.output;
    public String toString() {
	switch (type) {
	case TID_BIGINT:
	    return "\\bigint";
	case TID_REAL:
	    return "\\real";
	default:
	    fail();
	    return "";//super.toString();
	}
    }

    /**
     * Returns the Java type that will be used to represent values of
     * <code>this</code> type.
     */
    public CType javaType() {
	switch (type) {
	case TID_BIGINT:
	    return JmlStdType.Bigint;
	case TID_REAL:
	    return CStdType.Double; // !FIXME! temporary.
	default:
	    fail();
	    return this;
	}
    }

    /**
     * Transforms this type to a string
     */
    public String getSignature() {
	switch (type) {
	case TID_BIGINT:
	    return "G";
	case TID_REAL:
	    return "R";
	default:
	    return super.getSignature();
	}
    }

    /**
     * Transforms this type to a string
     */
    public void appendSignature(FastStringBuffer buff) {
	char	c;

	switch (type) {
	case TID_BIGINT:
	    c = 'G';
	    break;
	case TID_REAL:
	    c = 'R';
	    break;
	default:
	    super.appendSignature(buff);
	    return;
	}
	buff.append(c);
    }

    /**
     * Returns the size used in stack by value of this type
     */
    public int getSize() {
	return 2; // valid? Should have no effect since no code is generated
		  // for \bigint and \real.
    }

    /**
     * Check if this type is an integral type.
     * @return is this a integral type ?
     */
    //@ pure
    public boolean isOrdinal() {
	switch (type) {
	case TID_BIGINT:
	    return true;
	case TID_REAL:
	    return false;
	default:
	    return super.isOrdinal();
	}
    }

    /**
     * Check if this type is a floating point type.
     * @return is this a floating point type?
     */
    //@ pure
    public boolean isFloatingPoint() {
	switch (type) {
	case TID_BIGINT:
	    return false;
	case TID_REAL:
	    return true;
	default:
	    return super.isFloatingPoint();
	}
    }

    // ----------------------------------------------------------------------
    // BODY CHECKING
    // ----------------------------------------------------------------------
    
    /** Returns true iff <code>from</code> type can be converted by widening
     * primitive conversion to <code>this</code> type. */
    /*@ also public normal_behavior
      @  requires true;
      @  ensures  \result <== (*
      @   (from is byte && this is \bigint, or \real) ||
      @   (from is short && this is \bigint, or \real) ||
      @   (from is char && this is \bigint, or \real) ||
      @   (from is int && this is \bigint, or \real) ||
      @   (from is long && this is \bigint, or \real) ||
      @   (from is float && this is \real) ||
      @   (from is double && this is \real) ||
      @   (from is \bigint && this is \real) *)
      @  && !\result <== (*
      @    (from is float && this is \bigint) ||
      @    (from is double && this is \bigint) 
      @  *);
      @*/
    public /*@pure@*/ boolean widening_primitive_conv_from(/*@non_null@*/ CType from) {
	return (from == CStdType.Float  && this == JmlStdType.Bigint ||
		from == CStdType.Double && this == JmlStdType.Bigint)
	    ? false
	    : super.widening_primitive_conv_from(from);
    }

}
