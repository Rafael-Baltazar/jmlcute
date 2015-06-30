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
 * $Id: Node.java,v 1.1 2003/02/21 15:15:40 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.util.Enumeration;

/**
Node is the basis of the tree that will be built. The tree serves as the
data structue used to control the enabling/disabling of the checks of 
components in addition, it will contain locations of classes that can be
loaded by the custom classloader.
*/
public interface Node {

    /* set and get names */
	/**
	Every node has a name that corresponds to the file/directory od the
	class/package.
	*/
    public String getName();
    public void setName(String name);

    /* methods to determine checkability*/
	/**
	use isCheckable to determine whether this Node represents a package or
	class can be checked or not.
	*/
    public boolean isCheckable();
	/**
	When an instance of a class is loaded, isWrap() is used to determine 
	whether to wrap the component or not.
	*/
    public boolean isWrap();
	/**
	When a wrapper calls a method on the wrapped object, this method
	is used to determine whether to check the preconditions first.
	*/
    public boolean isCheckPrecondition();
	/**
	When a wrapper calls a method on the wrapped object, this method
	is used to determine whether to check the postconditions after.
	*/
    public boolean isCheckPostcondition();
	/**
	When a wrapper calls a method on the wrapped object, this method
	is used to determine whether to check the invariants first.
	*/
    public boolean isCheckInvariant();

    /**
        @param propagate if set to true will also set the children.
    */
    public void setWrap(boolean b, boolean propagate);
    /**
        @param propagate if set to true will also set the children.
    */
    public void setCheckPrecondition(boolean b, boolean propagate);
    /**
        @param propagate if set to true will also set the children.
    */
    public void setCheckPostcondition(boolean b, boolean propagate);
    /**
        @param propagate if set to true will also set the children.
    */
    public void setCheckInvariant(boolean b, boolean propagate);

    /* methods to get, set and check status of children */
	/**
	Add a child node to this node.
	*/
    public void addChild(Node n);
	/**
	Given a name, get the child node.
	@return null if the name is not a child.
	*/
    public Node getChild(String name);
	/**
	returns an Enumeration of the names of the node's children.
	*/
    public Enumeration getKeys();
	/**
	returns an Enumeration of Nodes, which are this node's children.
	*/
    public Enumeration getChildren();
	/**
	returns true if the node has no children.
	*/
    public boolean isEmpty();

    /* methods to remove and otherwise mutate the tree */
    /**
        Does nothing if name is not a child.
    */
    public void removeChild(String name);
    /**
        removes extraneous nodes.
    */
    public boolean prune();

}

