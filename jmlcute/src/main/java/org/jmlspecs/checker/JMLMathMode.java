/*
 * Copyright (C) 2004 Iowa State University
 * 
 * This file is part of the MultiJava project. More information is available
 * from www.multijava.org.
 * 
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2 of the License, or (at your option) any later
 * version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA
 * 
 * $Id: JMLMathMode.java,v 1.2 2004/06/23 19:43:05 f_rioux Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.MJMathMode;

public class JMLMathMode extends MJMathMode {

	public static JMLMathMode newJMLMathMode(byte mm) {
		return new JMLMathMode(mm, true);
	}

	public static JMLMathMode newJMLMathMode() {
		return new JMLMathMode(DEFAULT, false);
	}

	private JMLMathMode(byte mm, boolean isSet) {
		super(mm);
		isModeExplicitlySet = isSet;
	}

	public boolean isExplicitlySet() {
		return isModeExplicitlySet;
	}

	protected boolean isModeExplicitlySet;

}
