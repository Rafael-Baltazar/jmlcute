/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
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
 * @author David Cok
 * $Id: JmlFileFinder.java,v 1.8 2006/11/28 20:06:36 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.util.classfile.ClassPath;

/** 
 * This FileFinder looks for a .class file and a .java file, returning
 * whichever one is newer.  */
public class JmlFileFinder extends org.multijava.mjc.AbstractFileFinder {

    static final String[] suffixes = { ".refines-java", ".refines-spec", 
				       ".refines-jml", ".java", ".spec", 
				       ".jml" };
    static final String[] suffixes1 = { ".java" };

    static final String SYMBOL_SUFFIX = ".sym";

    public JmlFileFinder() {}

    /* removed to disable cache
    private final static Hashtable fileCache = new Hashtable();
    private final static HashSet   fileNotFoundSet = initNotFoundHashSet();
    private final static String notFoundFileName="notFoundCache.tmp";
    private static HashSet initNotFoundHashSet() {
	    HashSet retVal = new HashSet();
	    java.io.File inFile = new java.io.File(notFoundFileName);
	    if (inFile.exists()) {
               java.io.BufferedReader in=null;
	       try {
	         in = new java.io.BufferedReader(new java.io.FileReader(notFoundFileName));
		 String line;
		 while ((line=in.readLine())!=null) {
			 retVal.add(line);
//System.out.println("adding '"+line+"'");
		 }
	       } catch (java.io.IOException ioe) {; 
	       } finally { try {if (in!=null) in.close(); } catch (java.io.IOException ioe2){;}}
	    }
//	    System.out.println("\n\n length is "+retVal.size()+"\n\n");
	    return retVal;
    }
    public static void dumpNotFoundHashSet() {
            java.util.Iterator elements = fileNotFoundSet.iterator();
	    java.io.File outFile=new java.io.File(notFoundFileName);
	    if (true || !outFile.exists()) {
	       java.io.PrintWriter out=null;
	       try {
	          out = new java.io.PrintWriter(new java.io.FileWriter(outFile));
	          while (elements.hasNext()) {
	   	        out.println(""+elements.next());
	          }
	       } catch (java.io.IOException ioe){;}
	       finally {
	          if (out!=null) out.close();
	       }
	    }
    }
    protected void finalize() {
	    dumpNotFoundHashSet();
    }
    private int   countCached;
    private int   countNeverFound;
    private int   countNotFoundNew;
    private int   countFoundNew;
    */
    /** 
     * This method finds a file for the given class name; it first
     * looks for a source file anywhere in the source path; if there
     * is none, then a class file is sought on the class path.  The
     * return value is null if no appropriate file could be found.  */
    //@ also
    //@ requires name != null; 
    public ClassPath.ClassDescription find(String name) {
	// first look for some sort of source file (anywhere on the
	// classpath) then look for a class file (anywhere on the
	// class path)

	//System.out.println("LOOKING FOR " + name);
	
	// is it in the cache?

        /* removed to disable cache
	if (fileNotFoundSet.contains(name)) {
//           countNeverFound++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
           return null;
	}
	ClassPath.ClassDescription classC = 
	    (ClassPath.ClassDescription) fileCache.get(name);
	if (classC != null) {
//	   countCached++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
           return classC; 
	}
	*/
	
        // read from symbol file?
        if (Main.hasOptionXsymr()) {
            ClassPath.ClassDescription classS = findSymbolFile(name);
            if (classS != null) {
//		countFoundNew++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
                /* removed to disable cache
	        fileCache.put(name, classS); 
		*/
                return classS;
            }
        }

	ClassPath.ClassDescription classJ = 
	    ClassPath.getSourceFile(sourceFilePrefixFor(name), suffixes);
	//System.out.println("SOURCE " + (classJ != null) + " " +
	//classJ.toString());
	if (classJ != null) { 
//	   countFoundNew++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
           /* removed to disable cache
	   fileCache.put(name, classJ); 
	   */
	   return classJ; 
	}

	ClassPath.ClassDescription classD = ClassPath.getClassPathFile(name);
	//System.out.println("CLASS FOUND " + (classD != null));
	if (classD != null) { 
//	   countFoundNew++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
           /* removed to disable cache
	   fileCache.put(name, classD); 
	   */
	   return classD; 
	}
//        countNotFoundNew++;
//	System.out.println("find: "+countNotFoundNew+" - "+countFoundNew+" - "
//			           +countCached+" - "+countNeverFound);
        /* removed to disable cache
	fileNotFoundSet.add(name);
	*/
//	System.out.println("notFound: '"+name+"'");
	return null;
    }

    /** 
     * Finds a source file per the implemented search order, which is
     * to search for all the suffixes in each directory on the source
     * path in turn.  Returns null if not found.  */
    //@ also
    //@ requires name != null;
    public ClassPath.ClassDescription findSourceFile(String name) {
        //System.out.println("LOOKING FOR " + name);
   	return ClassPath.getSourceFile(sourceFilePrefixFor(name), suffixes);
    }       
    
    /**
     * Returns the symbol file for the given class name. If no symbol
     * file is found or the symbol file isn't up to date with respect
     * to source files, null is returned.
     */
    private ClassPath.ClassDescription findSymbolFile(String name) {
        ClassPath.ClassDescription classS 
                = ClassPath.getClassPathFile(name, SYMBOL_SUFFIX);
        if (classS != null) {
            // compare the time stamp with those of source files if any
            String pname = sourceFilePrefixFor(name);
            for (int i = 0; i < suffixes.length; i++) {
                ClassPath.ClassDescription classJ = 
                    ClassPath.getFile(pname, suffixes[i]);
                if (classJ != null && 
                    classJ.getTime() > classS.getTime()) {
                    return null;
                }
            }
        }
        return classS;
    }
}
