//Copyright (C) 2007 Universidade De Pernambuco (UPE)

//This file is part of the runtime library of the Java Modeling Language With AspectJ.

package org.jmlspecs.ajmlrac.runtime;

/**
 * A JML error class to notify internal precondition violations.  An
 * internal precondition violation refers to a precondition violation
 * that arises inside the execution of the method that we are
 * interested in.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.2$
 */

public class JMLInternalPreconditionError extends JMLPreconditionError {

	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	public JMLInternalPreconditionError(String message) {
		super(message);
	}
	
	/**
	 * Creates a new instance.
	 */
	public JMLInternalPreconditionError(String message, String methodName)
	{
		super(message, methodName);
	}
	
	public JMLInternalPreconditionError(String message, JMLInternalPreconditionError e) {
		super(message+"\n\n"+e.toString());
	}
	
	public JMLInternalPreconditionError(Throwable cause) {
		super(cause);
	}
}
