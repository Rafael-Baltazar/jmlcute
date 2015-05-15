/* 
 * Copyright (C) 2000-2001 Virginia Tech
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
 * $Id: Location.java,v 1.1 2003/02/21 15:15:40 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

/**
Location contains all pertinent information to get at a class in the filesystem
(or in a Jar file).
*/
public class Location {

    private Node node;

    private String jarLocation = null;

    /**
    location is where the class is located. If the class is in a jar, this
    is relative to the jar file. If the class is in the filesystem, this is
    an absolute path.
    */
    private String location = null;
    

    /* Getters and setters */
    /**
    jarLocation is where the jarfile containing the class is located.
	@return null if the class is not in a Jar file (ie a file in the filesystem)
    */
    public String getJarLocation() {
        return jarLocation;
    }
    /**
    location is where the class is located. If the class is in a jar, this
    is relative to the jar file. If the class is in the filesystem, this is
    an absolute path.
    */
    public String getLocation() {
        return location;
    }

    public void setJarLocation(String loc) {
        jarLocation = loc;
    }

    public void setLocation(String loc) {
        location = loc;
    }

    public Node getNode() {
        return node;
    }

    public Location(Node n) {
        node = n;
    }
}
