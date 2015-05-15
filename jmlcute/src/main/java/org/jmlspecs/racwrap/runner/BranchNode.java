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
 * $Id: BranchNode.java,v 1.1 2003/02/21 15:15:39 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.util.Enumeration;
import java.util.Hashtable;

/**
BranchNode is an implementation of Node for branches. 
BranchNode uses nested hashtables to implement Node.
*/
public class BranchNode extends CommonImpl implements Node {

    public BranchNode() {
        this.setCheckable(true);
    }

    /*Fields*/
    private Hashtable children = new Hashtable();

    /* methods to get, set and check status of children */
    public void addChild(Node n) {
        children.put(n.getName(), n);
    }

    public Node getChild(String name) {
        return (Node) children.get(name);
    }

    public Enumeration getKeys() {
        return children.keys();
    }

    public Enumeration getChildren() {
        return children.elements();
    }

    public boolean isEmpty() {
        return children.isEmpty();
    }

    public void removeChild(String name) {
        children.remove(name);
    }

    public boolean prune() {
        //base case
        if(this.isEmpty()) 
            return true;

        boolean result = true;
        Enumeration e = children.keys();
        while(e.hasMoreElements()) {
            String key = (String) e.nextElement();
            Node n = (Node) children.get(key);
            if(n.prune() == false) {
                result = false;
            } else {
                this.removeChild(key);
            }
        }

        return result;
    }
}
