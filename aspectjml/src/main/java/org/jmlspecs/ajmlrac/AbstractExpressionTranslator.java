/* $Id: AbstractExpressionTranslator.java,v 1.1 2005/12/02 01:54:52 f_rioux Exp $
 *
 * Copyright (C) 2005 Iowa State University
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
 */

package org.jmlspecs.ajmlrac;

/**
 * This class is intended to be a common base class for both TransExpression
 * and TransExpression2. Its main purpose is to help in the adaptation of
 * the qexpr package to TransExpression2.
 * 
 * @author f_rioux
 */
public abstract /*@ non_null_by_default */
class AbstractExpressionTranslator extends RacAbstractVisitor {

}