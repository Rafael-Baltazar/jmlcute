/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AspectJML
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
 * $Id: AjmlracTask.java,v 1.0 2009/11/13 20:01:30 henriquerebelo Exp $
 * 
 * NOTE: This file is based on the original $Id: CompileTask.java,v 1.2 
 *       2002/12/15 19:52:22 leavens Exp $ 
 * 
 */

package org.jmlspecs.ant.taskdefs;

import org.apache.tools.ant.BuildException;

/** An Ant task to run Java app. compiled with ajmlc.
 * @version $Revision: 1.0 $
 * @author Henrique Rebelo
 */
public class AjmlracTask extends CommonOptionsTask {

	private boolean source;
	private String classname;

	public AjmlracTask() {
		super();
		source = false;
		classname = null;
	}
		
	public String getClassname() {
		return classname;
	}

	public void setClassname(String classname) {
		this.classname = classname;
	}

	/**
	 * Set the source generation property of this CompileTask.
	 *
	 * @param source
	 *        True if source should be generated, false otherwise.
	 */
	public void setSource(boolean source) {
		this.source = source;
	}

	/**
	 * Check whether or not this task will generate source instead
	 * of class files.
	 */
	public /*@ pure @*/ boolean getSource() {
		return source;
	}

	/**
	 * execute the ajmlc task - Rebelo
	 */
	public void execute() throws BuildException {
		try{
			executeJavaTask(getClassname());
		}
		catch(Exception exc) {
			throw new BuildException(exc);
		}
	}
	
	public void executeJavaTask(String classname) throws Exception {
		setupArguments(false);
		super.setClassname(classname);
		super.execute();
	}
}
