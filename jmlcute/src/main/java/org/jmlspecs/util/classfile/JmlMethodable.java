/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id: JmlMethodable.java,v 1.2 2003/11/15 06:20:11 leavens Exp $
 */

package org.jmlspecs.util.classfile;

/**
 * An interface for querying JML methods.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.2 $
 */

public interface JmlMethodable extends JmlModifiable {

    /** 
     * Returns true iff this method declaration is explicitly
     * annotated with the JML modifier <code>pure</code> or
     * inherits it from supertypes.
     */
    //@ assignable objectState;
    boolean isPure();
}
