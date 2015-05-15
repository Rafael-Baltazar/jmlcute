/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AspectJML
 *
 * AJML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * AJML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with AJML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: CommonOptionsTask.java,v 1.0 2009/11/13 10:45:36 henriquerebelo Exp $
 * 
 * NOTE: This file is based on the original $Id: CommonOptionsTask.java,v 1.3 
 *       2003/10/12 18:02:23 leavens Exp $
 * 
 */

package org.jmlspecs.ant.taskdefs;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Location;
import org.apache.tools.ant.taskdefs.Java;
import org.apache.tools.ant.types.FileSet;
import org.apache.tools.ant.types.Path;
import org.apache.tools.ant.types.Reference;
import org.apache.tools.ant.types.resources.FileResource;

/** An abstract Ant task that holds common options for the AspectJML tools
 *
 * @version $Revision: 1.0 $
 * @author Henrique Rebelo
 * @author  Marko van Dooren
 * @author Gary T. Leavens
 */
public class CommonOptionsTask extends Java {

	private boolean recursive;
	private boolean quiet;
	private boolean verbose;
	private Path classpath;
	private File destDir;
	private Path srcdir; // for .java, .jml, and .aj files
	private Path sourcepath; // also for .java, .jml, and .aj files

	//@ post !getVerbose() && !getRecursive();
	//@ post getFileSets() != null && getFileSets().isEmpty();
	public CommonOptionsTask() {
		reset();
	}

	public void reset() {
		this.destDir = null;
		this.quiet = false;
		this.verbose = false;
		this.recursive = false;
		this.srcdir = null;
		this.classpath = null;
	}   

	/**
	 * Return an array of the argument strings for running a JML tool.
	 */
	public void setupArguments(boolean isTypeCheckerOnly) throws Exception {
		if(getQuiet()) {
			super.createArg().setValue("-Q");
		}
		if(getVerbose()) {
			super.createArg().setValue("-v");
		}

		if(getRecursive()) {
			super.createArg().setValue("-R");
		}

		if(getClasspath() != null) {
			int count = 0;
			final StringBuffer code = new StringBuffer();
			super.createClasspath().add(getClasspath());
			super.createArg().setValue("-C");
			for (Iterator iterator = getClasspath().iterator(); iterator.hasNext();) {
				FileResource object = (FileResource) iterator.next();
				if(count == 0){
					code.append(object.getFile().getPath());
				}
				else{
					code.append(";").append(object.getFile().getPath());
				}
				count++;
			}
			super.createArg().setValue(code.toString());
		}

		if(getSourcepath() != null) {
			super.createArg().setValue("-S");
			super.createArg().setValue(getSourcepath().toString());
		}

		if(getDestdir() != null) {
			super.createArg().setValue("-d");
			super.createArg().setValue(getDestdir().getPath());
		}

		this.setToolSpecificOptions();

		if (srcdir != null) {
			String[] dirs = srcdir.list();
			List jmlFiles = new ArrayList();
			for (int i = 0; i < dirs.length; i++) {
				File dir = getProject().resolveFile(dirs[i]);
				check(dir, dirs[i], true, getLocation());
				FileSet fileset = new FileSet();
				fileset.setDir(dir);
				String[] files = fileset.getDirectoryScanner(getProject()).getIncludedFiles();
				
				for (int j = 0; j < files.length; j++) {
					File file = new File(dir, files[j]);
					if((file.getAbsolutePath().endsWith(".jml"))){
						super.createArg().setValue(file.getAbsolutePath());	
						jmlFiles.add(file.getAbsolutePath());
					}
					if((file.getAbsolutePath().endsWith(".java"))){
						if(!jmlFiles.contains(file.getAbsolutePath().replace(".java", ".jml"))){
							super.createArg().setValue(file.getAbsolutePath());	
						}		
					}
					if(!isTypeCheckerOnly){
						if((file.getAbsolutePath().endsWith(".aj"))){
							super.createArg().setValue(file.getAbsolutePath());	
							jmlFiles.add(file.getAbsolutePath());
						}
					}
				}
			}
		}   
		
		if (sourcepath != null) {
			String[] dirs = sourcepath.list();
			List jmlFiles = new ArrayList();
			for (int i = 0; i < dirs.length; i++) {
				File dir = getProject().resolveFile(dirs[i]);
				check(dir, dirs[i], true, getLocation());
				FileSet fileset = new FileSet();
				fileset.setDir(dir);
				String[] files = fileset.getDirectoryScanner(getProject()).getIncludedFiles();
				
				for (int j = 0; j < files.length; j++) {
					File file = new File(dir, files[j]);
					if((file.getAbsolutePath().endsWith(".jml"))){
						super.createArg().setValue(file.getAbsolutePath());	
						jmlFiles.add(file.getAbsolutePath());
					}
					if((file.getAbsolutePath().endsWith(".java"))){
						if(!jmlFiles.contains(file.getAbsolutePath().replace(".java", ".jml"))){
							super.createArg().setValue(file.getAbsolutePath());	
						}		
					}
					if(!isTypeCheckerOnly){
						if((file.getAbsolutePath().endsWith(".aj"))){
							super.createArg().setValue(file.getAbsolutePath());	
							jmlFiles.add(file.getAbsolutePath());
						}
					}
				}
			}
		}   
	}

	/**
	 * Prepare a list of the tool-specific options for running a JML tool.
	 */
	public void setToolSpecificOptions() {
	}

	/**
	 * Check whether or not this task works recursive.
	 */
	public /*@ pure @*/ boolean getRecursive() {
		return recursive;
	}

	/**
	 * Set the verbosity
	 *
	 * @param recursive
	 *        True if the task should work recursive, false otherwise.
	 */
	/*@
      @   post getRecursive() == recursive;
      @*/
	public void setRecursive(boolean recursive) {
		this.recursive = recursive;
	}

	/**
	 * Check whether or not this task should be verbose.
	 */
	public /*@ pure @*/ boolean getQuiet() {
		return quiet;
	}
	
	public /*@ pure @*/ boolean getVerbose() {
		return verbose;
	}

	/**
	 * Set the verbosity
	 *
	 * @param verbose
	 *        True if the task should be verbose, false otherwise.
	 */
	public void setQuiet(boolean quiet) {
		this.quiet = quiet;
	}
	
	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}

	public Path createClasspath() {
		if (classpath == null) {
			classpath = new Path(getProject());
		}
		return classpath.createPath();
	}        

	public void setClasspath(Path path) {
		classpath = incPath(classpath, path);
	}

	/**
	 * Return the classpath of this CheckTask.
	 */
	public /*@ pure @*/ Path getClasspath() {
		return this.classpath;
	}

	public void setClasspathref(Reference classpathref) {
		createClasspath().setRefid(classpathref);
	}

	/**
	 * Add path elements to source path and return result.
	 * Elements are added even if they do not exist.
	 * @param source the Path to add to - may be null
	 * @param toAdd the Path to add - may be null
	 * @return the (never-null) Path that results
	 */
	protected Path incPath(Path source, Path toAdd) {
		if (null == source) {
			source = new Path(getProject()); 
		}
		if (null != toAdd) {
			source.append(toAdd);
		}
		return source;
	}

	/**
	 * Set the destDir of this CompileTask.
	 *
	 * @param destination
	 *        A String containing the directory where the files
	 *        should be put.
	 */
	public void setDestdir(File destination) {
		destDir = destination;
	}

	/**
	 * Return the destDir of this CompileTask.
	 */
	public /*@ pure @*/ File getDestdir() {
		return destDir;
	}

	/**
	 * Set the sourcepath for the JML checker.
	 *
	 * @param sourcepath
	 *        The sourcepath.
	 */
	public void setSourcepath(Path sourcepath) {
		this.sourcepath = incPath(this.sourcepath, sourcepath);
	} 
	
	public void setSourcepathref(Reference sourcepathref) {
		createSourcePath().setRefid(sourcepathref);
	}

	/**
	 * Return the sourcepath of this CheckTask.
	 */
	public /*@ pure @*/ Path getSourcepath() {
		return sourcepath;
	}

	public Path createSrcdir() {
		if (srcdir == null) {
			srcdir = new Path(getProject());
		}
		return srcdir.createPath();
	}
	
	public Path createSourcePath() {
		if (sourcepath == null) {
			sourcepath = new Path(getProject());
		}
		return sourcepath.createPath();
	}

	public void setSrcDir(Path path) {
		this.srcdir = incPath(this.srcdir, path);
	}

	/** 
	 * Throw BuildException unless file is valid.
	 * @param file the File to check
	 * @param name the symbolic name to print on error
	 * @param isDir if true, verify file is a directory
	 * @param loc the Location used to create sensible BuildException
	 * @return
	 * @throws BuildException unless file valid
	 */
	protected final boolean check(File file, String name,
			boolean isDir, Location loc) {
		loc = loc != null ? loc : getLocation();
		if (file == null) {
			throw new BuildException(name + " is null!", loc);
		}
		if (!file.exists()) {
			throw new BuildException(file + " doesn't exist!", loc);
		}
		if (isDir ^ file.isDirectory()) {
			String e = file + " should" + (isDir ? "" : "n't")  +
			" be a directory!";
			throw new BuildException(e, loc);
		}
		return true;
	}
}
