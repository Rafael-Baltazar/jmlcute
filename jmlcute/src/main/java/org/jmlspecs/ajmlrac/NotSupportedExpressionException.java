// @(#)$Id: NotSupportedExpressionException.java,v 1.2 2005/11/10 21:25:50 f_rioux Exp $
//
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

package org.jmlspecs.ajmlrac;

import org.multijava.util.compiler.TokenReference;

/**
 * This is exception is used to report not supported expressions when 
 * encountered during the visit of the tree. Since method signature are
 * inherited from the default RAC visitor, the exception has to be runtime.
 * 
 * @author Frederic Rioux
 * @version $Revision: 1.2 $
 */
public class NotSupportedExpressionException extends PositionnedExpressionException 
{
//	private TokenReference tok;
	
	public NotSupportedExpressionException(TokenReference tok, String msg){
		super(tok, msg);
	}

}