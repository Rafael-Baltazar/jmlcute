package org.jmlspecs.ajmlrac.runtime;


class JMLSatisfiedXPostconditionSignalsOnly extends JMLPostconditionError {
	
	long visibility;

	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	public JMLSatisfiedXPostconditionSignalsOnly(String message) {
		super(message);
	}
	
	/**
     * Creates a new instance.
     */
    public JMLSatisfiedXPostconditionSignalsOnly(String message, String methodName, long visibility)
    {
        super(message, methodName);
        this.visibility = visibility; 
    }
	
	public JMLSatisfiedXPostconditionSignalsOnly(Throwable cause) {
		super(cause);
	}
}
