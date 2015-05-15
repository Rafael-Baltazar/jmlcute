//Copyright (C) 2010 Federal University of Pernambuco (UFPE)

//This file is part of the runtime library of the Java Modeling Language With AspectJ.

package org.jmlspecs.ajmlrac.runtime;

/**
 * A JML error class to notify internal precondition violations.  An
 * internal precondition violation refers to a precondition violation
 * that arises inside the execution of the method that we are
 * interested in.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.1$
 */

public class JMLInternalProtectedPreconditionError extends JMLInternalPreconditionError {

	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	public JMLInternalProtectedPreconditionError(String message) {
		super(message);
	}
	
	/**
	 * Creates a new instance.
	 */
	public JMLInternalProtectedPreconditionError(String message, String methodName)
	{
		super(message, methodName);
	}
	
	public JMLInternalProtectedPreconditionError(Throwable cause) {
		super(cause);
	}
}
