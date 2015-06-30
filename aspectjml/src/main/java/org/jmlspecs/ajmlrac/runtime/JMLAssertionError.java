// @(#)$Id: JMLAssertionError.java,v 1.8 2006/06/07 02:11:02 f_rioux Exp $

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
 * $Id: JMLAssertionError.java,v 1.0 2010/09/17 11:59:33 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: JMLAssertionError.java,v 1.8 2006/06/07 02:11:02 f_rioux Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac.runtime;

/**
 * An abstract error class to notify all kinds of runtime assertion
 * violations.
 *
 * part of the original JMLAssertionError file by Yoonsik Cheon
 *
 *  @author Henrique Rebelo
 *  @version $Revision: 1.2 $
 */
public abstract class JMLAssertionError extends Error
{
	
	/** Name of the method that contains the violated assertion. 
     * It can be <code>null</code> if the assertion is not associated
     * with any particular methods, e.g., invariants or history constraints.
     */
    /*@ spec_public @*/ protected String methodName;
   
	/**
	 * Creates a new instance from the given assertion message error. 
	 */
	protected JMLAssertionError(String message) {
		super(message);
		this.methodName = "";
	}
	
	protected JMLAssertionError(Throwable cause) {
		super(cause.getMessage(), cause);
		this.methodName = "";
	}
}
