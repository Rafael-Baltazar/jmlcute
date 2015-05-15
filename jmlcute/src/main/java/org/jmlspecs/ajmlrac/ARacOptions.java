/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AJML
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
 * $Id: ARacOptions.java,v 1.0 2009/03/27 16:48:06 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ARacOptions extends RacOptions {

	private List javaFilePaths = new ArrayList();
	private List aspectFilePaths = new ArrayList();
	private static String CLASSPATH_ARG = "-cp";
	private static String SOURCE_ARG = "-source";
	private static String DESTINATION_DIR_ARG = "-d";
	private static String EXT_OPT_ARG = "-ext";
	private static String INPATH_ARG = "-inpath";
	private static String OUTJAR_ARG = "-outjar";
	private static String ASPECTPATH_ARG = "-aspectpath";

	public ARacOptions(String name) {
		super(name);
	}

	public void addJavaFilePathToCompilation(String currentJavaFilePath){
		if(!this.javaFilePaths.contains(currentJavaFilePath)){
			javaFilePaths.add(currentJavaFilePath);
		}
	}

	public void addAspectFilePathToCompilation(String currentAspectFilePath){
		if(!this.aspectFilePaths.contains(currentAspectFilePath)){
			aspectFilePaths.add(currentAspectFilePath);
		}
	}
	
	public void addAspectFilePathToCompilation(String currentAspectFilePath, String fileName){
		if(!this.aspectFilePaths.contains(currentAspectFilePath)){
			boolean contains = false;
			String pathToRemove = "";
			for (Iterator iterator = aspectFilePaths.iterator(); iterator.hasNext();) {
				String currentAspectFilePathFromList = (String) iterator.next();
				if(currentAspectFilePathFromList.endsWith(fileName)){
					contains = true;
					pathToRemove = currentAspectFilePathFromList;
				}
			}
			if(contains){
				aspectFilePaths.remove(pathToRemove);
				aspectFilePaths.add(currentAspectFilePath);
			}	
			else{
				aspectFilePaths.add(currentAspectFilePath);
			}
		}
	}

	public String[] generateArgsForAjcCompiler(String destination,
			String classpath, String source, String inpath, String outjar, String aspectpath, boolean showWeaveInfo) {
		
		List argsList = new ArrayList();

		for (int i = 0; i < javaFilePaths.size(); i++) {
			String currentTempFile = (String)javaFilePaths.get(i);
			argsList.add(currentTempFile);
		}

		for (int i = 0; i < aspectFilePaths.size(); i++) {
			String currentTempFile = (String) aspectFilePaths.get(i);
			argsList.add(currentTempFile);
		}

		if (classpath != null){
			argsList.add(CLASSPATH_ARG);
			argsList.add(classpath);
		}
		
		if (source != null){
			argsList.add(SOURCE_ARG);
			argsList.add(source);
		}

		if (inpath != null){
			argsList.add(INPATH_ARG);
			argsList.add(inpath);
		}
		
		if (aspectpath != null){
			argsList.add(ASPECTPATH_ARG);
			argsList.add(aspectpath);
		}
			
		if (outjar != null){
			argsList.add(OUTJAR_ARG);
			argsList.add(outjar);
		}

		if (destination != null){
			argsList.add(DESTINATION_DIR_ARG);
			argsList.add(destination);
		}
		
		// overWeaving if needed... [[[hemr]]] --- not needed anymore... this really complicates inpath [[[hemr]]]
//		if(inpath != null){
//			argsList.add("-Xset:overWeaving=true");
//		}
		
		if(showWeaveInfo){
			argsList.add("-showWeaveInfo");	
		}
		else {
			// removing ajc -Xlint:warnings
			argsList.add("-Xlint:ignore");
		}

		String [] args = new String[argsList.size()];
		for (int i = 0; i < args.length; i++) {
			args[i] = (String) argsList.get(i);
		}
		return args;
	}

	public String [] generateArgsForAbcCompiler(String destination, String classpath){
		List argsList = new ArrayList();

		for (int i = 0; i < javaFilePaths.size(); i++) {
			String currentTempFile = (String)javaFilePaths.get(i);
			argsList.add(currentTempFile);
		}

		for (int i = 0; i < aspectFilePaths.size(); i++) {
			String currentTempFile = (String) aspectFilePaths.get(i);
			argsList.add(currentTempFile);
		}

		if (classpath != null){
			argsList.add(CLASSPATH_ARG);
			argsList.add(classpath);
		}

		if (destination != null){
			argsList.add(DESTINATION_DIR_ARG);
			argsList.add(destination);
		}

		String [] args = new String[argsList.size()];
		for (int i = 0; i < args.length; i++) {
			args[i] = (String) argsList.get(i);
		}
		return args;
	}

	public String [] generateArgsForAbcJaCompiler(String destination, String classpath, String injars){
		int contOpArgs = 0;
		if(destination != null){
			contOpArgs ++;
		}
		if(classpath != null){
			contOpArgs ++;
		}

		String [] args = new String[((javaFilePaths.size()+aspectFilePaths.size())+(contOpArgs*2))+2];
		int filesLength = (javaFilePaths.size()+aspectFilePaths.size());

		for (int i = 0; i < javaFilePaths.size(); i++) {
			String currentTempFile = (String)javaFilePaths.get(i);
			args[i] = currentTempFile;
		}

		for (int i = 0; i < aspectFilePaths.size(); i++) {
			String currentTempFile = (String) aspectFilePaths.get(i);
			args[i+javaFilePaths.size()] = currentTempFile;
		}

		if (classpath != null){
			args[filesLength+0] = CLASSPATH_ARG;
			args[filesLength+1] = classpath;	
		}

		if (destination != null){
			args[filesLength+2] = DESTINATION_DIR_ARG;
			args[filesLength+3] = destination;
			args[filesLength+4] = EXT_OPT_ARG;
			args[filesLength+5] = "abc.ja";
		}
		else{
			args[filesLength+2] = EXT_OPT_ARG;
			args[filesLength+3] = "abc.ja";
		}

		return args;
	}

	public List getAspectFilePaths() {
		return aspectFilePaths;
	}
	
	public List getJavaFilePaths() {
		return javaFilePaths;
	}

}
