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
 * $Id: Main.java,v 1.3 2003/05/02 14:05:53 flyingroc Exp $
 */


package org.jmlspecs.racwrap.runner;

import java.lang.reflect.*;
import java.io.*;
import java.util.*;
import java.awt.event.*;
import java.awt.*;

import javax.swing.*;

//import org.jmlspecs.jmlrac.runtime.*;


public class Main implements ActionListener {

    public static void main(String args[]) throws Exception {

        //Get the CLASSPATH directories.
        String loc_str = System.getProperty("java.class.path");
        String path_separator = System.getProperty("path.separator");
        StringTokenizer strTok = new StringTokenizer(loc_str, path_separator);
        String[] locs = new String[strTok.countTokens()];

        for(int i = 0; strTok.hasMoreElements(); i++) {
            locs[i] = strTok.nextToken();
        }

        //Get properties
        Properties chxProps = getProperties();
 
        //Get additional paths from properties
        loc_str = chxProps.getProperty("locations");
        strTok = new StringTokenizer(loc_str, path_separator);
        String[] locs2 = new String[locs.length + strTok.countTokens()];
        for(int i = 0; i < locs.length; i++) {
            locs2[i] = locs[i];
        }

        for(int i = locs.length; strTok.hasMoreElements(); i++) {
            locs2[i] = strTok.nextToken();
        }

        //Create the tree
        Node node = TreeBuilder.buildTree(locs2);

        //Create the classloader
        ClassLoader cloader = new ChxClassLoader(node);

        String[] prog_args = new String[args.length - 1];
        for(int i = 0; i < prog_args.length; i++) {
           prog_args[i] = args[i+1];
        }

        //Create the tree UI
        TreeViewer viewer = new TreeViewer(node);

        JFrame frame = new JFrame("Tree Viewer");
        frame.getContentPane().add(viewer, BorderLayout.CENTER);
        
        JButton go = new JButton("Go");
        go.addActionListener(new Main(args[0], prog_args, cloader));
        frame.getContentPane().add(go, BorderLayout.SOUTH);
            
        //Finish setting up the frame, and show it.
        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                System.exit(0);
            }
        });

        frame.setSize(300,400);

        frame.show();
    }

    /**
    Get properties from the default properties file.
    */
    public static Properties getProperties() {
        return getProperties("chx.props");
    }

    /**
    Get properties from a specific properties file
    */

    public static Properties getProperties(String filename) {
        Properties default_props = new Properties();
        default_props.setProperty("locations", "");
        Properties rval = new Properties(default_props);
        try {
            rval.load(new FileInputStream(filename));
        } catch (Exception e) {
            System.out.println("Warning: could not load " + filename + " using default properties.");
        }

        return rval;
    }

    /**
    Run the program
    */
    public void runProgram(  String name, 
                                    String[] args, 
                                    ClassLoader loader) throws Exception {

        Class c = loader.loadClass(name);
        //System.out.println("loaded " + name);
        Class[] classes = new Class[] {new String[0].getClass()};
        Object[] args2 = {args};
        try {
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
        }
    }

    public void runProgram() throws Exception {
        runProgram(name, args, loader);
    }


    private String name = null;
    private String[] args = null;
    private ClassLoader loader = null;
    private boolean running = false;

    public Main(String name, String[] args, ClassLoader loader) {

        this.name = name;
        this.args = args;
        this.loader = loader;

    }

    public void actionPerformed(ActionEvent e) {
        if(lockRunning()) {
            try {
                runProgram(name, args, loader);
            } catch(Exception error) {
                System.out.println(error);
                error.printStackTrace();
            }
            unlockRunning();
        }
    }

    private synchronized boolean lockRunning() {
        if(running) 
            return false;
        else {
            running = true;
            return true;
        }
    }

    private synchronized void unlockRunning() {
        running = false;
    } 
}
