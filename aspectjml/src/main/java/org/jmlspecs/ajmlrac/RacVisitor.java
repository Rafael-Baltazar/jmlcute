/*
 * Copyright (C) 2001-2002 Iowa State University
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
 * $Id: RacVisitor.java,v 1.3 2002/09/18 16:06:52 cheon Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlVisitor;

/**
 * An implementation of the Visitor Design Pattern [GoF94] for the JML
 * runtime assertion checker.  This interface defines two additional
 * visitor methods for RAC-specific nodes.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */
public interface RacVisitor extends JmlVisitor, RacConstants {

    /** Visits the given RAC predicate, <code>self</code>. */
    void visitRacPredicate( /*@ non_null@*/ RacPredicate self );

    /** Visits the given RAC node, <code>self</code>. */
    void visitRacNode( /*@ non_null@*/ RacNode self );
}
