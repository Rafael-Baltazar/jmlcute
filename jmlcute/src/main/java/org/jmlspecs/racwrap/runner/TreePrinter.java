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
 * $Id: TreePrinter.java,v 1.1 2003/02/21 15:15:40 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.util.Enumeration;

/**
Methods to print the tree to standard output.
*/

public class TreePrinter {

    public static void print(Node node) {
        print(node, 0);
    }

    public static void print(Node node, int level) {
        

        for(int i = 0; i < level; i++) {
            System.out.print("    ");
        }

        System.out.println(node.toString());

        if(! (node instanceof Leaf)) {
            Enumeration e = node.getChildren();
            while(e.hasMoreElements()) {
                Node child = (Node) e.nextElement();
                print(child, level + 1);

            }
        }
    }
}
