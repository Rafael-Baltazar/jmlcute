/*
 * Copyright (C) 2013 Federal University of Pernambuco and 
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
 * $Id: XCSCrossRef.java,v 1.0 2013 henriquerebelo Exp $
 * 
 * 
 */

package org.jmlspecs.ant.taskdefs;

import org.apache.tools.ant.BuildException;

/** An Ant task to run the AspectJML cross ref generator.
 * @version $Revision: 1.0 $
 * @author Henrique Rebelo
 * @author  Marko van Dooren
 */
public class XCSCrossRefTask extends CommonOptionsTask {
	
	private static final String CLASSNAME = "org.jmlspecs.crossref.Main";
  
    public XCSCrossRefTask() {
        super();
    }

    /**
	 * execute the ajmlc task - Rebelo
	 */
	public void execute() throws BuildException {
		try{
			executeJavaTask(CLASSNAME);
		}
		catch(Exception exc) {
			throw new BuildException(exc);
		}
	}
	
	public void executeJavaTask(String classname) throws Exception {
		setupArguments(true);
		super.setClassname(CLASSNAME);
		super.execute();
	}

}
