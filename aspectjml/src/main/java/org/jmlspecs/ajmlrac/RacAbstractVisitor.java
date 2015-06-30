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
 * $Id: RacAbstractVisitor.java,v 1.3 2003/06/17 03:30:43 cruby Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.Constants;
import org.jmlspecs.checker.JmlAbstractVisitor;

/**
 * A default implementation for the RacVisitor interface. This is an
 * abstract JML visitor class to facilitate writing concrete visitor
 * classes. Each visitor method defined in this class performs no
 * action. A concrete subclass should override them appropriately.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.3 $
 */
public abstract class RacAbstractVisitor extends JmlAbstractVisitor 
    implements Constants, RacVisitor {

    
    /**
     * Visits the given RAC predicate, <code>self</code>. By default,
     * this method does not perform any actions at all, so it must be
     * appropriately overriden by a concrete subclass.
     */
    public void visitRacPredicate( /*@ non_null@*/ RacPredicate self ) {
    }

    /**
     * Visits the given RAC node, <code>self</code>. By default, this
     * method does not perform any actions at all, so it must be
     * appropriately overriden by a concrete subclass.
     */
    public void visitRacNode( /*@ non_null@*/ RacNode self ) {
    }
}

