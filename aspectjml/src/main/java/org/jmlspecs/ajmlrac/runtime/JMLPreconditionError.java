/* $Id: JMLPreconditionError.java,v 1.4 2006/06/07 02:11:03 f_rioux Exp $
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
 * A JML exception class for notifying precondition violations.
 * The runtime assertion checker makes a distinction among precondition
 * violations: <em>internal precondition violations</em> and
 * <em>entry precondition violations</em>.
 * An internal precondition violation refers to a precondition violation
 * that arises inside the execution of the method, say <em>M</em>, that
 * we are interested in. An entry precondition violation refers to a
 * violation concerned with the method <em>M</em>'s precondition.
 *
 * @see JMLInternalPreconditionError
 * @see JMLEntryPreconditionError
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.2 $
 */
public abstract class JMLPreconditionError extends JMLAssertionError 
{
	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	protected JMLPreconditionError(String message) {
		super(message);
	}
	
	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	protected JMLPreconditionError(String message, String methodName) {
		super(message);
		this.methodName = methodName;
	}

	protected JMLPreconditionError(Throwable cause) {
		super(cause);
	}

}
