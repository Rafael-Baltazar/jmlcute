//Copyright (C) 2007 Universidade De Pernambuco (UPE)

//This file is part of the runtime library of the Java Modeling Language With AspectJ.


package org.jmlspecs.ajmlrac.runtime;

/**
 * A JML error class to notify internal normal postcondition violations.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.2$
 */
public class JMLInternalExceptionalPostconditionError extends JMLExceptionalPostconditionError {

	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	public JMLInternalExceptionalPostconditionError(String message) {
		super(message);
	}
	
	/**
	 * Creates a new instance.
	 */
	public JMLInternalExceptionalPostconditionError(String message, String methodName, Throwable cause)
	{
		super(message, methodName, cause);
	}
	
	public JMLInternalExceptionalPostconditionError(Throwable cause) {
		super(cause);
	}
}
