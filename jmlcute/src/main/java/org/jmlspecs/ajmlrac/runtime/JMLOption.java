/* $Id: JMLOption.java,v 1.4 2005/07/07 21:03:01 leavens Exp $
 *
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
 */

package org.jmlspecs.ajmlrac.runtime;

/** 
 * An interface to provide compile-time and runtime options. The
 * compile-time options chooses the kinds of assertions for which
 * assertion check code be generated, and the runtime options are for
 * reporting and recovering assertion violations. These options are
 * arranged so that runtime subset can be easily determined. That is
 * if the run-time option is ALL but the compile-time option was
 * PRECONDITIONS_ONLY, then at run-time, only PRECONDITIONS can be
 * checked. This validity can be found out by just comparing numerical
 * values.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.4 $
 */

public interface JMLOption {

    // ----------------------------------------------------------------------
    // COMPILE-TIME OPTIONS
    // ----------------------------------------------------------------------

    /** 
     * Indicates that no assertion check code is generated at compile time,
     * and thus no check at runtime.
     */ 	
    int NONE = 0;

    /** 
     * Indicates that only precondition check code is generated at
     * compile-time, and only precondition check is performed at runtime.
     */
    int PRECONDITIONS_ONLY = 1;

    /** 
     * Indicates that all assertion check code is generated at
     * compile-time and all are checked at runtime.
     */
    int ALL  = Integer.MAX_VALUE;
}
