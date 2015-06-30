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
 * $Id: Wrapper.java,v 1.3 2003/03/21 19:48:43 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner;

/**
 *  This class is the root of the inheritance hierarchy of wrappers.
 *  If the original source class extends object, then the wrapper class
 *  will extend Wrapper.
 */

public class Wrapper {
    public Wrapped _wrapped_object = null;
    public Node access = null;
}
