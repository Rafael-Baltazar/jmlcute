/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of the JML project.
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
 * $Id: Constants.java,v 1.24 2007/04/18 23:04:37 leavens Exp $
 */

package org.jmlspecs.checker;

/**
 * Defines all additional constants shared by JML package files.
 */
public interface Constants extends org.multijava.mjc.Constants {

    // ----------------------------------------------------------------------
    // TYPE IDENTIFIER
    // ----------------------------------------------------------------------
    /*@ public invariant
	TID_LONG   < TID_BIGINT &&
	TID_DOUBLE < TID_REAL &&
	TID_BIGINT < TID_REAL;
     @*/

    int TID_TYPE		= 100;
    int TID_BIGINT		= 101;
    int TID_REAL		= 102;

    // ----------------------------------------------------------------------
    // ARITHMETHIC MODE IDENTIFIERS
    // ----------------------------------------------------------------------
    
    // 16 and under are reserved by superinterface
    byte AMID_BIGINT_MATH = 17;

    // ----------------------------------------------------------------------
    // JML CONSTANTS
    // ----------------------------------------------------------------------
 
    String JML_JMLObjectSet	= "org/jmlspecs/models/JMLObjectSet";

    // ----------------------------------------------------------------------
    // MODIFIER FLAGS, used in masks with inherited ACC_* flags
    // ----------------------------------------------------------------------
    // See org.multijava.mjc.Constants

    long ACC_MODEL			= 0x00000001L << 16;
  //long ACC_PURE			= 0x00000002L << 16; WMD: see org.multijava.mjc.Constants.
    long ACC_INSTANCE			= 0x00000004L << 16;
    long ACC_SPEC_PUBLIC		= 0x00000008L << 16;
    long ACC_SPEC_PROTECTED		= 0x00000010L << 16;
    long ACC_GHOST			= 0x00000020L << 16;
    long ACC_MONITORED			= 0x00000040L << 16;
    long ACC_UNINITIALIZED		= 0x00000080L << 16;
  //long ACC_NOT_CURRENTLY_USED		= 0x00000100L << 16;
    long ACC_HELPER			= 0x00000200L << 16;
    long ACC_CODE_JAVA_MATH		= 0x00000400L << 16;
    long ACC_CODE_SAFE_MATH		= 0x00000800L << 16;
    long ACC_CODE_BIGINT_MATH		= 0x00001000L << 16;
    long ACC_SPEC_JAVA_MATH		= 0x00002000L << 16;
    long ACC_SPEC_SAFE_MATH		= 0x00004000L << 16;
    long ACC_SPEC_BIGINT_MATH		= 0x00008000L << 16;
  //long ACC_NULLITY_MODIFIERS		= 0x000x0000L << 16; see org.multijava.mjc.Constants.
    long ACC_QUERY			= 0x00100000L << 16;
    long ACC_SECRET			= 0x00200000L << 16;
    long ACC_CODE			= 0x00400000L << 16;
    long ACC_EXTRACT                    = 0X00800000L << 16;

    int ACC2_RAC_METHOD		= 0x00000001; // FIXME - mode into ACC_ list as an internal flag.

    /**
     * These arrays are used to map flags to names for pretty printing
     * and error messages and to issue style warnings for modifiers
     * out of order. 
     *
     * @see #ACCESS_FLAG_ARRAY
     * @see #ACCESS_FLAG_NAMES
     */
    long[] ACCESS_FLAG_ARRAY =
	new long[] { 
	    ACC_PUBLIC,
	    ACC_PRIVATE,
	    ACC_PROTECTED,
	    ACC_SPEC_PUBLIC,
	    ACC_SPEC_PROTECTED,
	    ACC_ABSTRACT,
	    ACC_STATIC,
	    ACC_MODEL,               
	    ACC_GHOST,               
	    ACC_PURE,                
	    ACC_QUERY,                
	    ACC_SECRET,                
	    ACC_FINAL,
	    ACC_SYNCHRONIZED,
	    ACC_INSTANCE,            
	    ACC_TRANSIENT,
	    ACC_VOLATILE,
	    ACC_NATIVE,
	    ACC_STRICT,
	    ACC_MONITORED,           
	    ACC_UNINITIALIZED,       
	    ACC_HELPER,
	    ACC_INTERFACE,
	    ACC_CODE_JAVA_MATH,
	    ACC_CODE_SAFE_MATH,
	    ACC_CODE_BIGINT_MATH,
	    ACC_SPEC_JAVA_MATH,
	    ACC_SPEC_SAFE_MATH,
	    ACC_SPEC_BIGINT_MATH,
	    ACC_NON_NULL,
	    ACC_NULLABLE,
 	    ACC_NULLABLE_BY_DEFAULT,
 	    ACC_NON_NULL_BY_DEFAULT,
	    ACC_CODE,
            ACC_EXTRACT,
	};

    /**
     * These arrays are used to map flags to names for pretty printing
     * and error messages and to issue style warnings for modifiers
     * out of order. 
     *
     * @see #ACCESS_FLAG_ARRAY
     * @see #ACCESS_FLAG_NAMES
     */
    String[] ACCESS_FLAG_NAMES =
	new String[] {
	    "public",
	    "private",
	    "protected",
	    "spec_public",
	    "spec_protected",
	    "abstract",
	    "static",
	    "model",               
	    "ghost",               
	    "pure",                
            "query",
            "secret",
	    "final",
	    "synchronized",
	    "instance",            
	    "transient",
	    "volatile",
	    "native",
	    "strictfp",
	    "monitored",           
	    "uninitialized",       
	    "helper",
	    "",		 // interface flag is suppressed for pretty printing
	    "code_java_math",
	    "code_safe_math",
	    "code_bigint_math",
	    "spec_java_math",
	    "spec_safe_math",
	    "spec_bigint_math",
	    "non_null",
	    "nullable",
 	    "nullable_by_default",
 	    "non_null_by_default",
	    "code",
	    "extract",
	};

    // ----------------------------------------------------------------------
    // OPERATORS
    // ----------------------------------------------------------------------

    // int OPE_POSTDEC		= 25;   // last inherited operator flag
    int OPE_L_ARROW         	= 26;	// "<-"  	
    int OPE_R_ARROW         	= 27;	// "->"  	
    int OPE_EQUIV           	= 28;	// "<==>"  	
    int OPE_NOT_EQUIV       	= 29;	// "<=!=>"  	
    int OPE_IMPLIES	        = 30;	// "==>" 	
    int OPE_BACKWARD_IMPLIES	= 31;	// "<==" 	

    int OPE_FORALL		= 32;	// \forall
    int OPE_EXISTS		= 33;	// \exists
    int OPE_MAX			= 34;	// \max
    int OPE_MIN			= 35;	// \min
    int OPE_NUM_OF		= 36;	// \num_of
    int OPE_PRODUCT		= 37;	// \product
    int OPE_SUM			= 38;	// \sum

    int OPE_SUBTYPE		= 39;	// "<:"

    // ----------------------------------------------------------------------
    // MODEL TYPES
    // ----------------------------------------------------------------------

    /** Used in typechecking set comprehension expressions. */
    String TN_JMLOBJECTSET = "org/jmlspecs/models/JMLObjectSet";

    /** Used in typechecking set comprehension expressions. */
    String TN_JMLVALUESET  = "org/jmlspecs/models/JMLValueSet";

    /** Used in typechecking set comprehension expressions. */
    String TN_JMLTYPE  = "org/jmlspecs/models/JMLType";

    // ----------------------------------------------------------------------
    // JML Expression Keywords
    // ----------------------------------------------------------------------

    public final int NOTHING = 1;
    public final int EVERYTHING = 2;
    public final int NOT_SPECIFIED = 3;
    public final int SAME = 4;
}

