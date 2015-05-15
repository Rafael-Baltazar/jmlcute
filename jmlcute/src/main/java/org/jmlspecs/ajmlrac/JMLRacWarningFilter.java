// @(#)$Id: JMLRacWarningFilter.java,v 1.2 2005/11/21 17:49:11 f_rioux Exp $

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


package org.jmlspecs.ajmlrac;

import org.jmlspecs.ajmlrac.RacMessages;
import org.jmlspecs.checker.JMLDefaultWarningFilter;
import org.multijava.util.compiler.CWarning;

/** A warning filter for JML.
 * @author Gary T. Leavens
 */
public class JMLRacWarningFilter extends JMLDefaultWarningFilter {

    // ----------------------------------------------------------------------
    // FILTER
    // ----------------------------------------------------------------------

    /**
     * Filters a warning
     * @param	warning		a warning to be filtred
     * @return	FLT_REJECT, FLT_FORCE, FLT_ACCEPT
     */
    public int filter(/*@ non_null @*/ CWarning warning) {
        int action = super.filter(warning);
        if (action == FLT_REJECT) {
            return action;
        }
        if ( warning.hasDescription(RacMessages.MAY_NOT_EXECUTABLE)
             || warning.hasDescription(RacMessages.NOT_EXECUTABLE)
             || warning.hasDescription(RacMessages.NOT_SUPPORTED_ALT) ) {
            return FLT_FORCE;
        }

	return action;
    }
}
