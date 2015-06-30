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
 * $Id: JmlModifiable.java,v 1.1 2003/11/14 21:58:20 cheon Exp $
 */

package org.jmlspecs.util.classfile;

/**
 * An interface for querying JML modifiers such as <code>model</code>.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.1 $
 */

public interface JmlModifiable {

    /** 
     * Returns true iff this declaration is explicitly annotated with
     * the JML modifier <code>model</code>.
     */
    /*@ pure @*/ boolean isModel();

    /** 
     * Returns true iff this declaration is explicitly annotated with
     * the JML modifier <code>ghost</code>.
     */
    /*@ pure @*/ boolean isGhost();

    /**
     * Returns true iff this declaration should be treated as a model
     * declaration; the declaration itself is annotated with the model
     * (or ghost) modifier or it is declared inside a model class or
     * interface.
     */
    /*@ pure @*/ boolean isEffectivelyModel();
}
