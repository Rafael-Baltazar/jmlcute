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
 * $Id: Leaf.java,v 1.1 2003/02/21 15:15:40 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.util.*;
/**
	Leaf is an implementation of Node for leaves. As leaves have no children
	it does not use the hastable implementation of BranchNode.
    Leaves also contain information about the location of various classes
    associated with the component the leaf represents.
*/
public class Leaf extends CommonImpl implements Node {

    private Location original = null;
    private Location wrapper = null;
    private Location statics = null;
    private Location iface = null;

    //This is only temporary, until we can have bytecode transformation going.
    public Location shadow = null;

	/**
	Location of the original class (X.class)
	*/
    public Location getOriginal() {
        return original;
    }
	/**
	Location of the wrapper class (X.wrap.chx)
	*/
    public Location getWrapper() {
        return wrapper;
    }

	/**
	Location of the statics class (X.statics.chx)
	*/
    public Location getStatics() {
        return statics;
    }

	/**
	Location of the interface.class (X.iface.chx)
	*/
    public Location getInterface() {
        return iface;
    }

    public void setOriginal(Location loc) {
        original = loc;
    }
    
    public void setWrapper(Location loc) {
        wrapper = loc;
    }

    public void setStatics(Location loc) {
        statics = loc;
    }

    public void setInterface(Location loc) {
        iface = loc;
    }

    /* methods to get, set and check status of children */
    /**
        Will throw an exception, leafs cannot have children.
    */
    public void addChild(Node n) {
        throw new RuntimeException("Cannot add to leaf");
    }

    /**
        alwya returns null.
    */
    public Node getChild(String name) {
        System.out.println("Warning: trying to get child of Leaf node.");
        return null;
    }

    /**
        always returns null.
    */
    public Enumeration getChildren() {
        System.out.println("Warning: trying to get Children of Leaf node.");
        return null;
    }

    /**
        always returns null.
    */
    public Enumeration getKeys() {
        System.out.println("Warning: trying to get keys of Leaf node.");
        return null;
    }

    /**
        always returns true.
    */
    public boolean isEmpty() {
        return true;
    }

    /* methods to remove and otherwise mutate the tree */
    /**
        Does nothing.
    */
    public void removeChild(String name) {
        System.out.println("Warning: removing child from a leaf, ignoring.");
        return;
    }

    /**
        removes extraneous nodes.
    */
    public boolean prune() {
        return false;
    }

}

