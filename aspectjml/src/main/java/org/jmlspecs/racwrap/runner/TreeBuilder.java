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
 * $Id: TreeBuilder.java,v 1.2 2004/01/22 20:00:15 leavens Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.jar.*;

/**
Treebuilder has static methods to build a tree from specified locations.
The treebuilder expects the file structure to be in this form: if there is a
class called X originally, the original untransformed class would be in a file
called X.class. Inm addition there will be three other files, X.iface.chx,
X.wrap.chx, and X.statics.chx.
*/

public class TreeBuilder {

    //print the tree;
	/**
	The main program takes in strings of paths to the root of package 
	hierarchies, either a directory or a jar file.
	*/
    public static void main(String[] args) {
        TreePrinter.print(buildTree(args));
    }

    /**
        Creates a tree given an array of paths to directories and jarfiles
        @param locations contains locations of the classfiles, as in the CLASSPATH
    */
    public static Node buildTree(String[] locations) {

        Node result = new BranchNode();
        result.setName("/");

        for(int i = 0; i < locations.length; i++) {
            File file = null;
            try {
                file = new File(locations[i]);
            } catch (Exception e) {
                System.out.println("Warning: could not locate: " + locations[i]);
                System.out.println(e);
                continue; //this is not a file, ignore
            }

            if(file == null) {
                System.out.println("Warning: could not locate: " + locations[i]);
                System.out.println("(file is null)");
                continue; //this is not a file, ignore
            }

            if(file.isDirectory()) {
                buildFileTree(result, file);
            } else {
                buildJarTree(result, file);
            }
        }

        result.prune();

        return result;
    }

    /**
        recursively builds the tree given a directory
    */
    public static void buildFileTree(Node parent, File file) {
        File[] subFiles = file.listFiles();

        for(int i = 0; i < subFiles.length; i++) {
            File f = subFiles[i];
//            System.out.println("Processing: " + f);
            Node childNode = null;
            if(f.isDirectory()) {
                childNode = getOrCreateBranch(parent,f.getName());
                buildFileTree(childNode, f);
            } else {
                Location loc = updateLeafNode(parent, f.getName());
                if(loc != null) {
                    try {
                        loc.setLocation(f.getCanonicalPath());
                    } catch (IOException e) {
                        System.out.println("Error setting the path of: " + f);
                        loc.setLocation("");
                    }
                }
            }
        }
    }

    /**
        builds the Jarfile tree.
    */
    public static void buildJarTree(Node parent, File file) {
        JarFile jFile = null;
        try {
            jFile = new JarFile(file);
        } catch (Exception e) {
            System.out.println("Warning: " + file + " is not a jar file. Ignoring.");
            return;
        }

        Enumeration e = jFile.entries();
        while(e.hasMoreElements()) {
            JarEntry jEntry = (JarEntry) e.nextElement();
 
            //directories will get created when the files are created.
            if(jEntry.isDirectory() || jEntry.getName().startsWith("META-INF")) {
                continue;
            }

            StringTokenizer strTok = new StringTokenizer(jEntry.getName(), "/");
            int numTokens = strTok.countTokens() - 1;

            Node current = parent;
            for(int i = 0; i < numTokens; i++) {
                String dir = strTok.nextToken();
                Node child = current.getChild(dir);
                if(child == null) {
                    child = new BranchNode();
                    child.setName(dir);
                    current.addChild(child);
                }
                current = child;
            }

            //now we have the name of the file
            String name = strTok.nextToken();
            Location loc = null;
            loc = updateLeafNode(current, name);
            if(loc != null) {
                loc.setLocation(jEntry.getName());
                try {            
                    loc.setJarLocation(file.getCanonicalPath());
                } catch (Exception ex) {
                    System.out.println("Error trying to get path of: " + file);
                    System.out.println(ex);
                    loc.setJarLocation("");
                }
            }
        }
    }

    /**
        updateLeafNode looks at the filename, determines if it is needed for
        our framework, and creates or updates a leaf node as needed. 
        @return returns a Location object so the caller can update the location
    */
    public static Location updateLeafNode(Node parent, String fname) {
        String classname = null;
        Leaf childNode = null;
        Location loc = null;
        
        if(fname.endsWith(".class")) {
            classname = fname.substring(0, fname.length() - 6);
            childNode = getOrCreateLeaf(parent, classname);
            loc = childNode.getOriginal();
            if(loc == null) {
                loc = new Location(childNode);
                childNode.setOriginal(loc);
            }
        } else if(fname.endsWith(".iface.chx")) {
            classname = fname.substring(0, fname.length() - 10);
            childNode = getOrCreateLeaf(parent, classname);
            childNode.setCheckable(true);
            loc = childNode.getInterface();
            if(loc == null) {
                loc = new Location(childNode);
                childNode.setInterface(loc);
            }
        } else if(fname.endsWith(".wrap.chx")) {
            classname = fname.substring(0, fname.length() - 9);
            childNode = getOrCreateLeaf(parent, classname);
            loc = childNode.getWrapper();
            if(loc == null) {
                loc = new Location(childNode);
                childNode.setWrapper(loc);
            }
        } else if(fname.endsWith(".statics.chx")) {
            classname = fname.substring(0, fname.length() - 12);
            childNode = getOrCreateLeaf(parent, classname);
            loc = childNode.getStatics();
            if(loc == null) {
                loc = new Location(childNode);
                childNode.setStatics(loc);
            }
       } else if(fname.endsWith(".shadow")) {
            classname = fname.substring(0, fname.length() - 7);
            childNode = getOrCreateLeaf(parent, classname);
            loc = childNode.shadow;
            if(loc == null) {
                loc = new Location(childNode);
                childNode.shadow = loc;
            }
        } else {
            //we don't know this file,
            return null;
        }

        return loc;
    }

    /**
    This method also adds the leaf node to the parent, if necessary
    */

    public static Leaf getOrCreateLeaf(Node parent, String classname) {
        Leaf leaf = (Leaf) parent.getChild(classname);
        if(leaf == null) {
            leaf = new Leaf();
            leaf.setName(classname);
            parent.addChild(leaf);
        }
        return leaf;
    }

    public static BranchNode getOrCreateBranch(Node parent, String name) {

       Node branch = parent.getChild(name);

       if(branch == null || branch instanceof Leaf) {
            if(branch instanceof Leaf) {
                System.out.println("Warning, naming conflict, replacing class " 
                                + name + " with package.");
            }
            branch = new BranchNode();
            branch.setName(name);
            parent.addChild(branch);
        }
        return (BranchNode) branch;
    }

}
