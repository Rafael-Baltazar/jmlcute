/** @(#)$Id: JMLRacUtil.java,v 1.4 2007/06/29 22:15:22 chalin Exp $
 *
 * Utility methods in support of RAC tests.
 *
 * @author Patrice Chalin (chalin@dsrg.org)
 * @version $Revision: 1.4 $
 */

package org.jmlspecs.ajmlrac.runtime;

public class JMLRacUtil {

	private JMLRacUtil() {
	}

	// FIXME: this should be factored out into a separate class.
	public static boolean nonNullElements(/*@nullable*/ Object a[]) {
		if(a == null)
			return false;
		for(int i = 0; i < a.length; i++) {
			if(a[i] == null)
				return false;
		}
		return true;
	}

	public static boolean newSem() {
	    return !oldSem();
	}

	public static boolean oldSem() {
	    String flags = System.getProperty("org.jmlspecs.ajmlc.flags");
	    boolean result = flags != null && flags.indexOf("-O") >= 0;
	    return result;
	}

	public static boolean matchCause(Class c, JMLAssertionError e) {
		return e.getCause() != null
				&& c.isAssignableFrom(e.getCause().getClass());
	}

	/**
	 * Under the old semantics, ensure that e is an instance of c.
	 * Under the new semantics, ensure that e is an instance of
	 * JMLEvaluationError and [soon to be added] that
	 * e.cause() is an instance of c.
	 */
	public static boolean checkErr(Class c, JMLAssertionError e) {
		
		if (!JMLAssertionError.class.isAssignableFrom(c))
			throw new IllegalArgumentException();
		//@ assert \typeof(c) <: \type(JMLAssertionError);
		if (oldSem()) {
			return c.isAssignableFrom(e.getClass());
		} else {
			return e instanceof JMLEvaluationError && matchCause(c, e);
		}
	}

}

// Copyright (C) 2006 Iowa State University
//
// This file is part of JML
//
// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.
//
// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
