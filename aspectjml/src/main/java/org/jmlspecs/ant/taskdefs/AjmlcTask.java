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
 * $Id: AjmlcTask.java,v 1.0 2009/11/13 10:52:36 henriquerebelo Exp $
 * 
 * 
 */

package org.jmlspecs.ant.taskdefs;

import java.util.Iterator;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.types.Path;
import org.apache.tools.ant.types.Reference;
import org.apache.tools.ant.types.resources.FileResource;

/** An Ant task to run the AspectJML runtime assertion checking compiler.
 * @version $Revision: 3.0 $
 * @author Henrique Rebelo
 * @author  Marko van Dooren
 */
public class AjmlcTask extends CommonOptionsTask {

	private boolean print; // -P
	private String source; // --source
	private boolean defaultNonNull; // -n
	private boolean noRepresentsError; // -M
	private boolean noExecutionSiteInstrumenation; // -y
	private boolean callSiteInstrumenation; // -b
	private boolean clientAwareChecking; // -B
	private boolean multipleSpecCaseChecking; // -l
	private boolean crosscuttingContractSpecifications; // -X
	private boolean adviceChecking; // -O
	private boolean showWeaveInfo; // -u
	
	private boolean quietTypeCheckInfo; // -Q
	private boolean quietCompPasses; // -q
	private boolean assignable; // -a
	private boolean debug; // -c
	private boolean mustBeExecutable; // -V
	private boolean noRedundancy; // -Y:
	private boolean noWrite; // -W
	private boolean purity; // -p
	private String warning; // -w
	
	private Path inpath; // -I
	private String outjar; // -i
	private String ajweaver; // -H
	private Path aspectpath; // -F
	private Path crossrefs; // -o
	private static final String CLASSNAME = "org.jmlspecs.ajmlrac.Main";
	private static final String DEFAULT_AJWEAVER = "ajc";
	private static final String DEFAULT_SOURCE = "1.7";
	private static final String DEFAULT_WARNING_PICKINESS = "1";

	public AjmlcTask() {
		super();
		this.print = false;
		this.source = AjmlcTask.DEFAULT_SOURCE;
		this.defaultNonNull = true;
		this.noExecutionSiteInstrumenation = false;
		this.callSiteInstrumenation = false;
		this.clientAwareChecking = false;
		this.multipleSpecCaseChecking = false;
		this.crosscuttingContractSpecifications = true;
		this.adviceChecking = true;
		this.inpath = null;
		this.outjar = "";
		this.aspectpath = null;
		this.crossrefs = null;
		this.ajweaver = AjmlcTask.DEFAULT_AJWEAVER;
		// recently added
		this.noRepresentsError = false; // -M
		this.showWeaveInfo = false; // -u
		this.quietTypeCheckInfo = false; // -Q
		this.quietCompPasses = true; // -q
		this.assignable = true; // -a
		this.debug = false; // -c
		this.mustBeExecutable = false; // -V
		this.noRedundancy = false; // -Y:
		this.noWrite = false; // -W
		this.purity = true; // -p
		this.warning = AjmlcTask.DEFAULT_WARNING_PICKINESS; // -w
	}
	
	/**
	 * @return the showWeaveInfo
	 */
	public boolean getShowWeaveInfo() {
		return showWeaveInfo;
	}

	/**
	 * @param showWeaveInfo the showWeaveInfo to set
	 */
	public void setshowWeaveInfo(boolean showWeaveInfo) {
		this.showWeaveInfo = showWeaveInfo;
	}
	
	/**
	 * @return the quietTypeCheckInfo
	 */
	public boolean getQuietTypeCheckInfo() {
		return quietTypeCheckInfo;
	}

	/**
	 * @param quietTypeCheckInfo the quietTypeCheckInfo to set
	 */
	public void setQuietTypeCheckInfo(boolean quietTypeCheckInfo) {
		this.quietTypeCheckInfo = quietTypeCheckInfo;
	}

	/**
	 * @return the quietCompPasses
	 */
	public boolean getQuietCompPasses() {
		return quietCompPasses;
	}

	/**
	 * @param quietCompPasses the quietCompPasses to set
	 */
	public void setQuietCompPasses(boolean quietCompPasses) {
		this.quietCompPasses = quietCompPasses;
	}

	/**
	 * @return the noRepresentsError
	 */
	public boolean getNoRepresentsError() {
		return noRepresentsError;
	}

	/**
	 * @param noRepresentsError the noRepresentsError to set
	 */
	public void setNoRepresentsError(boolean noRepresentsError) {
		this.noRepresentsError = noRepresentsError;
	}

	/**
	 * @return the assignable
	 */
	public boolean getAssignable() {
		return assignable;
	}

	/**
	 * @param assignable the assignable to set
	 */
	public void setAssignable(boolean assignable) {
		this.assignable = assignable;
	}

	/**
	 * @return the debug
	 */
	public boolean getDebug() {
		return debug;
	}

	/**
	 * @param debug the debug to set
	 */
	public void setDebug(boolean debug) {
		this.debug = debug;
	}

	/**
	 * @return the mustBeExecutable
	 */
	public boolean getMustBeExecutable() {
		return mustBeExecutable;
	}

	/**
	 * @param mustBeExecutable the mustBeExecutable to set
	 */
	public void setMustBeExecutable(boolean mustBeExecutable) {
		this.mustBeExecutable = mustBeExecutable;
	}

	/**
	 * @return the noRedundancy
	 */
	public boolean getNoRedundancy() {
		return noRedundancy;
	}

	/**
	 * @param noRedundancy the noRedundancy to set
	 */
	public void setNoRedundancy(boolean noRedundancy) {
		this.noRedundancy = noRedundancy;
	}

	/**
	 * @return the noWrite
	 */
	public boolean getNoWrite() {
		return noWrite;
	}

	/**
	 * @param noWrite the noWrite to set
	 */
	public void setNoWrite(boolean noWrite) {
		this.noWrite = noWrite;
	}

	/**
	 * @return the purity
	 */
	public boolean getPurity() {
		return purity;
	}

	/**
	 * @param purity the purity to set
	 */
	public void setPurity(boolean purity) {
		this.purity = purity;
	}

	/**
	 * @return the warning
	 */
	public String getWarning() {
		return warning;
	}

	/**
	 * @param warning the warning to set
	 */
	public void setWarning(String warning) {
		this.warning = warning;
	}

	/**
	 * @return the defaultNonNull
	 */
	public boolean getDefaultNonNull() {
		return defaultNonNull;
	}

	/**
	 * @param defaultNonNull the defaultNonNull to set
	 */
	public void setDefaultNonNull(boolean defaultNonNull) {
		this.defaultNonNull = defaultNonNull;
	}

	/**
	 * @return the callSiteInstrumenation
	 */
	public boolean getNoExecutionSiteInstrumenation() {
		return noExecutionSiteInstrumenation;
	}

	/**
	 * @param noExecutionSiteInstrumenation the noExecutionSiteInstrumenation to set
	 */
	public void setNoExecutionSiteInstrumenation(boolean noExecutionSiteInstrumenation) {
		this.noExecutionSiteInstrumenation = noExecutionSiteInstrumenation;
	}

	/**
	 * @return the callSiteInstrumenation
	 */
	public boolean getCallSiteInstrumenation() {
		return callSiteInstrumenation;
	}

	/**
	 * @param callSiteInstrumenation the callSiteInstrumenation to set
	 */
	public void setCallSiteInstrumenation(boolean callSiteInstrumenation) {
		this.callSiteInstrumenation = callSiteInstrumenation;
	}
	
	/**
	 * @return the clientAwareChecking
	 */
	public boolean getClientAwareChecking() {
		return clientAwareChecking;
	}
	
	/**
	 * @param clientAwareChecking the clientAwareChecking to set
	 */
	public void setClientAwareChecking(boolean clientAwareChecking) {
		this.clientAwareChecking = clientAwareChecking;
	}

	/**
	 * @return the multipleSpecCaseChecking
	 */
	public boolean getMultipleSpecCaseChecking() {
		return multipleSpecCaseChecking;
	}

	/**
	 * @param multipleSpecCaseChecking the multipleSpecCaseChecking to set
	 */
	public void setMultipleSpecCaseChecking(boolean multipleSpecCaseChecking) {
		this.multipleSpecCaseChecking = multipleSpecCaseChecking;
	}
	
	/**
	 * @return the crosscuttingContractSpecifications
	 */
	public boolean getCrosscuttingContractSpecifications() {
		return crosscuttingContractSpecifications;
	}

	/**
	 * @param crosscutContractInterface the crosscutContractInterface to set
	 */
	public void setAdviceChecking(boolean adviceChecking) {
		this.adviceChecking = adviceChecking;
	}
	
	/**
	 * @return the crosscuttingContractSpecifications
	 */
	public boolean getAdviceChecking() {
		return adviceChecking;
	}

	/**
	 * @param crosscutContractInterface the crosscutContractInterface to set
	 */
	public void setCrosscuttingContractSpecifications(boolean crosscuttingContractSpecifications) {
		this.crosscuttingContractSpecifications = crosscuttingContractSpecifications;
	}

	/**
	 * Set the source generation property of this CompileTask.
	 *
	 * @param source
	 *        True if source should be generated, false otherwise.
	 */
	public void setSource(String source) {
		this.source = source;
	}

	/**
	 * Check whether or not this task will generate source instead
	 * of class files.
	 */
	public /*@ pure @*/ String getSource() {
		return source;
	}

	/**
	 * @return the print
	 */
	public boolean getPrint() {
		return print;
	}

	/**
	 * @param print the print to set
	 */
	public void setPrint(boolean print) {
		this.print = print;
	}

	public Path getInpath() {
		return inpath;
	}
	
	public Path createInpath() {
		if (inpath == null) {
			inpath = new Path(getProject());
		}
		return inpath.createPath();
	}   

	public void setInpath(Path path) {
		this.inpath = incPath(this.inpath, path);
	}
	
	public void setInpathref(Reference inpathref) {
		createInpath().setRefid(inpathref);
	}
	
	public String getAjweaver() {
		return ajweaver;
	}

	public void setAjweaver(String ajweaver) {
		this.ajweaver = ajweaver;
	}
	
	public String getOutjar() {
		return outjar;
	}

	public void setOutjar(String outjar) {
		this.outjar = outjar;
	}
	
	public Path getAspectpath() {
		return aspectpath;
	}
	
	public Path getCrossrefs() {
		return crossrefs;
	}
	
	public Path createAspectpath() {
		if (aspectpath == null) {
			aspectpath = new Path(getProject());
		}
		return aspectpath.createPath();
	}   

	public void setAspectpath(Path path) {
		this.aspectpath = incPath(this.aspectpath, path);
	}
	
	public void setCrossrefs(Path path){
		this.crossrefs = path;
	}
	
	public void setAspectpathref(Reference aspectpathref) {
		createInpath().setRefid(aspectpathref);
	}

	/**
	 * execute the ajmlc task - Rebelo
	 */
	public void execute() throws BuildException {
		try{
			executeJavaTask(CLASSNAME);
		}
		catch(Exception exc) {
			throw new BuildException(exc);
		}
	}

	/**
	 * Return a list of the tool-specific options for running a JML tool.
	 */
	public void setToolSpecificOptions() {
		if(getNoExecutionSiteInstrumenation()) {
			super.createArg().setValue("-y");
		}
		if(getCallSiteInstrumenation()) {
			super.createArg().setValue("-b");
		}
		if(getClientAwareChecking()) {
			super.createArg().setValue("-B");
		}
		if(getMultipleSpecCaseChecking()) {
			super.createArg().setValue("-l");
		}
		if(getCrosscuttingContractSpecifications()) {
			super.createArg().setValue("-X");
		}
		if(getAdviceChecking()) {
			super.createArg().setValue("-O");
		}
		if(!getDefaultNonNull()) {
			super.createArg().setValue("-n");
		}
		
		if(getQuietTypeCheckInfo()) {
			super.createArg().setValue("-Q");
		}
		
		if(!getQuietCompPasses()) {
			super.createArg().setValue("-q");
		}
		
		if(!getAssignable()) {
			super.createArg().setValue("-a");
		}
		
		if(getDebug()) {
			super.createArg().setValue("-c");
		}
		
		if(getShowWeaveInfo()) {
			super.createArg().setValue("-u");
		}
		
		if(getMustBeExecutable()) {
			super.createArg().setValue("-V");
		}
		
		if(getNoRepresentsError()) {
			super.createArg().setValue("-M");
		}
		
		if(getNoRedundancy()) {
			super.createArg().setValue("-Y");
		}
		
		if(getNoWrite()) {
			super.createArg().setValue("-W");
		}
		
		if(!getPurity()) {
			super.createArg().setValue("-p");
		}
		
		if(!(getWarning().equals(DEFAULT_WARNING_PICKINESS))){
			super.createArg().setValue("-w");
			super.createArg().setValue(getWarning());
		}
		
		if(getPrint()) {
			super.createArg().setValue("-P");
		}
		
		if(!(getSource().equals(DEFAULT_SOURCE))){
			super.createArg().setValue("--source");
			super.createArg().setValue(getSource());
		}
		
		if(getInpath() != null) {
			int count = 0;
			final StringBuffer code = new StringBuffer();
			super.createArg().setValue("--inpath");
			for (Iterator iterator = getInpath().iterator(); iterator.hasNext();) {
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
		
		if(getAspectpath() != null) {
			int count = 0;
			final StringBuffer code = new StringBuffer();
			super.createArg().setValue("--aspectpath");
			for (Iterator iterator = getAspectpath().iterator(); iterator.hasNext();) {
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
		
		if(getCrossrefs() != null) {
			int count = 0;
			final StringBuffer code = new StringBuffer();
			super.createArg().setValue("--crossrefs");
			for (Iterator iterator = getCrossrefs().iterator(); iterator.hasNext();) {
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
		
		if(!(getAjweaver().equals(DEFAULT_AJWEAVER))){
			super.createArg().setValue("-H");
			super.createArg().setValue(getAjweaver());
		}
		
		if(!(getOutjar().equals(""))){
			super.createArg().setValue("-i");
			super.createArg().setValue(getOutjar());
		}
	}
	
	public void executeJavaTask(String classname) throws Exception {
		setupArguments(false);
		super.setClassname(CLASSNAME);
		super.execute();
	}
}
