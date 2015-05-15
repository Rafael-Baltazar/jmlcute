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
 * $Id: ChxClassLoader.java,v 1.3 2003/05/09 03:31:58 flyingroc Exp $
 */

package org.jmlspecs.racwrap.runner; 

import java.io.*;
import java.util.*;
import java.util.jar.*;
import java.lang.reflect.*;

/**
ChxClassLoader is the custom classloader that will load the wrapper
classes when needed.
*/
public class ChxClassLoader extends ClassLoader {

    private Hashtable classes = new Hashtable();
    private Hashtable tree = null;

    /**
        Constructor. 
        @param root The root node of the tree.
    */
    public ChxClassLoader(Node root) {

        //create the lookup tree
        tree = new Hashtable();
        populate(tree, root); 
        //printTree(tree, 0);
    }

	
	/**
	The classloader does not use the Node directly, rather it creates
	a new tree based on the class tree. This is to make it easier to
	lookup names of classes. That is, "$chx_*" classes are not easily
	located in the original tree.
	*/
    private void populate(Hashtable lookupParent, Node nodeParent) {

        Enumeration e = nodeParent.getChildren();

        while(e.hasMoreElements()) {
            Node n = (Node) e.nextElement();
            String name = n.getName();
            if(n instanceof Leaf) {
                Leaf l = (Leaf) n;
                if(n.isCheckable()) {
                    //System.out.println(n);
                    lookupParent.put(name, l.getInterface());
                    //Get the shadow file...
                    try {
                        lookupParent.put("$chx_Orig_" + name, l.shadow);
                        lookupParent.put("$chx_Wrap_" + name, l.getWrapper());
                        lookupParent.put("$chx_Statics_" + name, l.getStatics());
                    } catch (NullPointerException ex) {
                        throw new RuntimeException("could not load" +
                                            " : " + name);
                    }
                } else {
                    lookupParent.put(name, l.getOriginal());
                }
            } else { //n is a branch node 
                Hashtable h = new Hashtable();
                lookupParent.put(name, h);
                populate(h, n);
            }
        }
    }

	/**
	Alias for loadClass(name, null);
	*/
    public Class loadClass(String name) throws ClassNotFoundException {
        return loadClass(name, false);
    }

	/**
	This classloader does *not* follow the Java ClassLoader delegation model.
	This is because we want to preempt the system classloader from loading
	the classes that are requested. 
	*/
    public synchronized Class loadClass(String name, boolean resolve) throws
        ClassNotFoundException {

        //first check the cache
        Class result = (Class) classes.get(name);
        if(result != null) {
            return result;
        }

        // next check if this is part of the base package. We use the system
        // classloader here because factory classes need to access instance of
        // Node, which has already been loaded by the system classloader.
        // If we load Node from our own classloader, there will be a type
        // error assigning to factory.node.//next check if this is part
        if( name.startsWith("org.jmlspecs.racwrap.runner.") 
            || name.startsWith("java.")) {
            result = super.findSystemClass(name);
        }

        //next try checking our tree
        if(result == null)
            result = loadClassFromTree(name);

        //Finally, as a last recourse we try using the parent classloader
        if(result == null) {
            try {
                result = super.findSystemClass(name);
            } catch (Exception e) {
                //do nothing
            }
        }

        if(result == null)
            throw new ClassNotFoundException("class: " + name + " not found.");

        classes.put(name, result);
        return result;
    }

	/**
	Given the name of a class, this method will find the location of 
	the class (if it knows about it), and load it.
	*/
    private Class loadClassFromTree(String name) {
        Class result = null;

        StringTokenizer strTok = new StringTokenizer(name, ".");
        int penultimate = strTok.countTokens() - 1;

        String current_name = null; 
        Hashtable current_node = tree;
        for(int i = 0; i < penultimate; i++) {
            current_name = strTok.nextToken();
            Object current_object = current_node.get(current_name);
            if(current_object == null || !(current_object instanceof Hashtable)) {
                return null;
            }

            current_node = (Hashtable) current_object;
        }

        current_name = strTok.nextToken();
        Object tmp = current_node.get(current_name);
        if(!(tmp instanceof Location))
            return null;

        //load the source
        Location loc = (Location) tmp;
        byte[] classData = getByteArray(loc);
        if(classData != null) {
            try {

                result = defineClass(name, classData, 0, classData.length, null);
            } catch (Error e) {
                System.out.println("Could not define class:" + name);
                e.printStackTrace();
                throw new RuntimeException("Could not define class:" + name);
            }
            if(current_name.startsWith("$chx_Statics_")) {
                try {
                    Field node_field = result.getField("access");
                    node_field.set(null,loc.getNode());
                } catch (Exception e) {
                    //System.out.println("Warning could not set node: " + name);
                    //System.out.println(e);
                    //System.out.println("node: " + loc.getNode());
                }
            }
        }

        return result;
    }

	/**
	Given the location of a class, return the contents of the file.
	@return returns an array of bytes that is the contents of the file.
	*/
    private byte[] getByteArray(Location loc) {
        byte result[] = null;
        InputStream istr = null;
        int size = 0;

        if(loc.getJarLocation() == null) {
            //this is a filesystem location
            try {
                istr = new FileInputStream(loc.getLocation());
                size = istr.available();
            } catch (Exception e) {
                System.out.println(e);
                return null;
            }
        } else {
            //this is a jar location
            try {
                JarFile jFile = new JarFile(loc.getJarLocation());
                JarEntry jEntry = jFile.getJarEntry(loc.getLocation());
                istr = new BufferedInputStream(jFile.getInputStream(jEntry));
                size = (int) jEntry.getSize();

             } catch (Exception e) {
                System.out.println(e);
                return null;
            }
        }

        try {
            result = new byte[size];
            istr.read(result);
            istr.close();
        } catch (IOException e) {
            System.out.println(e);
            return null;
        }
        return result;

    }

	/**
	prints the internal tree representation to stdout. Useful for debugging.
	*/
    public void printTree(Hashtable parent, int level) {

        Enumeration e = parent.keys();
        while(e.hasMoreElements()) {
            for(int i = 0; i < level; i++)
                System.out.print("    ");
            String key = (String) e.nextElement();
            System.out.println(key);
            Object obj = parent.get(key);
            if(obj instanceof Hashtable) {
                printTree((Hashtable) obj, level + 1);
            }
        }
    }

    public void printTree() {
        this.printTree(tree, 1);
    }
}
