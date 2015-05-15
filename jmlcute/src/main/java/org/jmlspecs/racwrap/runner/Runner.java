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
 * $Id: Runner.java,v 1.1 2003/05/02 14:05:54 flyingroc Exp $
 */
package org.jmlspecs.racwrap.runner;                          

import java.lang.reflect.*;                                   
import java.io.*;
import java.util.*;

public class Runner {

    private String name;
    private String[] prog_args;
    private boolean check;
    private ClassLoader cloader;

    public static Vector getClasspaths() {

        Vector rval = new Vector();
        String loc_str = System.getProperty("java.class.path");
        String path_separator = System.getProperty("path.separator");
        StringTokenizer strTok = new StringTokenizer(loc_str, path_separator);

        while(strTok.hasMoreElements()) {
            rval.addElement(strTok.nextElement());
        }
        return rval;
    }

    public Runner(String name, String[] prog_args, boolean check) {
        this.name = name;
        this.prog_args = prog_args;
        this.check = check;
    }

    public void run() {
        Node node = TreeBuilder.buildTree(toArray(getClasspaths()));
        if(check) {
            node.setWrap(true, true);
            node.setCheckPrecondition(true, true);
            node.setCheckPostcondition(true, true);        
            node.setCheckInvariant(true, true);
        }

        cloader = new ChxClassLoader(node);

        try {
            Class c = cloader.loadClass(name);
            //System.out.println("loaded " + name);
            Class[] classes = new Class[] {new String[0].getClass()};
            Object[] args2 = {prog_args};

            Method m = c.getDeclaredMethod("main", classes);
            if(m == null) {
                System.out.println("Class has no main method.");
            } else if (!Modifier.isStatic(m.getModifiers())) {
                System.out.println("main method is not static");
            } else {
                m.invoke(null, args2);                        
            }
        } catch (InvocationTargetException e) {               
            Throwable err = e.getTargetException();           
            //We cannot use instanceof bec. the err may be loaded by our    
            //different classloader                           
            System.out.println(err.getClass().toString());    
            if(err.getClass().toString().startsWith(
                    "class org.jmlspecs.jmlrac.runtime")) {
                System.out.println("JML assertion error:");   
                System.out.println(err.getMessage());         
            } else {                                          
                err.printStackTrace();                        
            }                                                 
        } catch (Exception other) {
            System.out.println("Error running program: " + name);
            other.printStackTrace();
        }
    }

    public static void main(String[] args) {
        //first parameter should be "check" or "nocheck"
        if(args.length < 2) {
            usage();
        }

        boolean b = false;
        if(args[0].equals("check")) {
           b = true; 
        } else if(args[0].equals("nocheck")) {
           b = false;
        } else {
            usage();
        }

        Vector v = new Vector();
        for(int i = 2; i < args.length; i++) {
            v.addElement(args[i]);
        }

        (new Runner(args[1], toArray(v),b)).run();

    }

    public static void usage() {
        System.out.println(
            "usage: java org.jmlspecs.runner.Runner <check | nocheck> <prog>" +
            "<args>");
        throw new RuntimeException("Invalid main arguments");
    }

    public static String[] toArray(Vector v) {
        String[] rval = new String[v.size()];
        for(int i = 0; i < v.size(); i++) {
            if(v.elementAt(i) instanceof String) {
                rval[i] = (String) v.elementAt(i);
            } else {
                System.out.println("elemen " +v.elementAt(i) + 
                    " is not a String"); 
            }
        }
        return rval;
    }
}
