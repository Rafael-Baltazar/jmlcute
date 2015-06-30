/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AJML
 *
 * AJML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * AJML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with AJML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: JMLEntryPreconditionError.java,v 1.0 2009/01/20 19:47:23 henriquerebelo Exp $
 */

//This file is part of the runtime library of the Java Modeling Language With AspectJ.

package org.jmlspecs.ajmlrac.runtime;

/**
 * A JML error class to notify entry precondition violations.  
 *
 * @see JMLInternalPreconditionError
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.1 $
 */

public class JMLEntryPreconditionError extends JMLPreconditionError {

	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	public JMLEntryPreconditionError(String message) {
		super(message);
	}
	
	/**
     * Creates a new instance.
     */
    public JMLEntryPreconditionError(String message, String methodName)
    {
        super(message, methodName);
    }
	
	public JMLEntryPreconditionError(Throwable cause) {
		super(cause);
	}
}
