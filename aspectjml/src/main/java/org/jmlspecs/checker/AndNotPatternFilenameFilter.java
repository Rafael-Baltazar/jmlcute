// @(#)$Id: AndNotPatternFilenameFilter.java,v 1.2 2005/05/12 00:18:28 f_rioux Exp $

// Copyright (C) 2004 Iowa State University

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

import java.io.File;
import java.io.FilenameFilter;
import java.util.regex.Pattern;

/** Decorates the file name filter given to the constructor so it
 * does not match names that include the pattern given to the constructor.
 * @author Gary T. Leavens
 */
public class AndNotPatternFilenameFilter implements FilenameFilter {

    /** The filter we are decorating */
    private /*@ non_null @*/ FilenameFilter parentFilter;

    /** The pattern we are excluding */
    private /*@ non_null @*/ Pattern excludePat;

    /** Initialize this filter.
     * @param f the filter to decorate
     * @param p the pattern of file names to exclude
     */
    //@ requires f != null && p != null;
    public AndNotPatternFilenameFilter(/*@non_null@*/ FilenameFilter f, /*@non_null@*/ String p) {
        parentFilter = f;
        excludePat = Pattern.compile(p);
    }

    /** Return true just when we want to process this file name.
     */
    public boolean accept(/*@non_null@*/ File dir, /*@non_null@*/ String name) {
        return parentFilter.accept(dir,name)
            && !excludePat.matcher(name).find();
    }
}
