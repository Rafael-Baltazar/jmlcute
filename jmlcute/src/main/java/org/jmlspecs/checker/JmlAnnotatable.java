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
 * $Id: JmlAnnotatable.java,v 1.2 2002/03/15 21:43:16 cclifton Exp $
 */

package org.jmlspecs.checker;


/**
 * This interface is implemented by AST nodes that can have child
 * nodes that represent JML annotations.  */
public interface JmlAnnotatable {
    /**
     * Returns an array of the JML annotations for this AST node.  The
     * array represents a forest of JML abstract syntax trees, one tree
     * for each annotation.  */
    JmlNode[] jmlAnnotations();
}
