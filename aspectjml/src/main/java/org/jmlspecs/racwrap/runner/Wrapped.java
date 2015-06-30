/* 
 * Copyright (C) 2003 Virginia Tech
 *
 * This file is part of JML
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
 * $Id: Wrapped.java,v 1.2 2003/03/19 01:41:31 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner;

/**
 *  This class is the root of the inheritance hierarchy of original objects.
 *  If the original source class extends object, then it will be transformed
 *  to extend Wrapped.
 */

public class Wrapped {
    public Object _chx_this = null;
    public Object chx_this = null;
}
