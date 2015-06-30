/*
// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.
 *
 * $Id: JMLNonExecutableException.java,v 1.5 2005/07/07 21:03:01 leavens Exp $
 */

package org.jmlspecs.ajmlrac.runtime;

/**
 * Thrown by generated runtime assertion check code to indicate that
 * an attempt has been made to execute a JML expression that is not
 * executable. The following expressions are statically determined to
 * be non-executable: 
 * <code>\not_modified</code>, <code>\fresh</code>, 
 * <code>(* ... *)</code>, <code>\invariant_for</code>,
 * <code>\is_initialized</code>, <code>\reach</code>,
 * <code>\elemtype</code>, and <code>\lockset</code>.  
 * For certain expressions such as quantified expressions,
 * executability is determined dynamically at runtime.
 * If an expression becomes non-executable, its value is contextually 
 * determined by the smallest, enclosing boolean expression. 
 * 
 * @see org.jmlspecs.jmlrac.TransExpressionForJmlc
 * @author Yoonsik Cheon
 * @version $Revision: 1.5 $
 */

public class JMLNonExecutableException extends java.lang.RuntimeException {

    /** Constructs a new instance. */
    public JMLNonExecutableException() {
	super();
    }

    /** Constructs a new instance with the given message,
     * <code>msg</code>. */
    public JMLNonExecutableException(String msg) {
	super(msg);
    }
}
