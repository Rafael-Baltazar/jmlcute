// @(#)$Id: JMLDefaultWarningFilter.java,v 1.6 2005/08/05 06:52:46 leavens Exp $

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

/** A warning filter for JML.
 * @author Gary T. Leavens
 */
public class JMLDefaultWarningFilter extends JMLWarningFilter {

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
        if ( warning.hasDescription(JmlMessages.MISSING_REPRESENTS) ) {
            return FLT_FORCE;
        }

	return action;
    }
}
