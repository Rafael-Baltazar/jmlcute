// @(#)$Id: JMLWarningFilter.java,v 1.9 2006/02/17 01:21:46 chalin Exp $

// Copyright (C) 2002 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


package org.jmlspecs.checker;

import org.multijava.util.compiler.CWarning;
import org.multijava.mjc.MjcMessages;

/** A warning filter for JML.
 * @author Gary T. Leavens
 */
public class JMLWarningFilter extends org.multijava.mjc.DefaultFilter {

    // ----------------------------------------------------------------------
    // FILTER
    // ----------------------------------------------------------------------

    /**
     * Filters a warning
     * @param	warning		a warning to be filtred
     * @return	FLT_REJECT, FLT_FORCE, FLT_ACCEPT
     */
    public int filter(/*@non_null*/ CWarning warning) {
        int action = super.filter(warning);
        if (action == FLT_REJECT) {
            return action;
        }
	if (warning.hasDescription(MjcMessages.METHOD_UNCHECKED_EXCEPTION)
	    || warning.hasDescription(MjcMessages.STRAY_COMMA)
            || warning.hasDescription(MjcMessages.COMPARING_BOOLEAN_CONSTANT)
            ) {
	    return FLT_REJECT;
	}
        if (warning.hasDescription(MjcMessages.CLASS_NAME_FILENAME)) {
            // !FIXME! should probably deal with the exact JML suffixes
            // instead of just worrying about .java files.
            if ( warning.getParams()[1].toString().endsWith(".java") ) {
                return FLT_ACCEPT;
            } else {
                return FLT_REJECT;
            }
        }
	return action;
    }
}
