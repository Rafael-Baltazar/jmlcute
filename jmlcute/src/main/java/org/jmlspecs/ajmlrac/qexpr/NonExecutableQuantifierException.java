/*
 * Copyright (C) 2001, 2002 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: NonExecutableQuantifierException.java,v 1.1 2002/07/21 17:22:37 cheon Exp $
 */

package org.jmlspecs.ajmlrac.qexpr;

/**
 * Thrown to indicate that an attempt has been made to translate a JML
 * quantified expression that is not executable.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.1 $
 */

public class NonExecutableQuantifierException extends Exception {

    /** Constructs a new instance. */
    public NonExecutableQuantifierException() {
	super();
    }

    /** Constructs a new instance with the given message. */
    public NonExecutableQuantifierException(String msg) {
	super(msg);
    }
}
