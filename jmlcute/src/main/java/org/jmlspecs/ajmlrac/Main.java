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
 * $Id: Main.java,v 1.0 2009/02/15 05:11:33 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: Main.java,v 1.76 2007/02/27 15:25:57 wdietl Exp $
 */

package org.jmlspecs.ajmlrac;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.OutputStream;
import java.io.Reader;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.jmlspecs.checker.JmlCommonOptions;
import org.jmlspecs.checker.JmlCompilationUnit;
import org.jmlspecs.checker.JmlMessages;
import org.jmlspecs.checker.JmlSourceClass;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CCompilationUnitContext;
import org.multijava.mjc.CCompilationUnitContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CompilerPassEnterable;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JavadocLexer;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.MjcLexer;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.MjcParser;
import org.multijava.mjc.ParsingController;
import org.multijava.mjc.TypeLoader;
import org.multijava.util.FormattedException;
import org.multijava.util.Utils;
import org.multijava.util.compiler.CompilerMessages;
import org.multijava.util.compiler.ModifierUtility;

import abc.main.CompilerAbortedException;
import abc.main.CompilerFailedException;

/**
 * A class implementing the entry point of the JML RAC compiler.
 *
 * @see org.jmlspecs.checker.Main
 * @see org.multijava.mjc.Main
 */
public class Main extends org.jmlspecs.checker.Main {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/** Constructs a JML RAC compiler with a default modifier utility. */
	public Main() {
		this(modUtil);
	}

	/** Constructs a JML RAC compiler with the given modifier utility,
	 * <code>modUtil</code>. */
	protected Main(ModifierUtility modUtil) {
		super(modUtil);

		setContextBehavior(
				new ContextBehavior(){
					public boolean noBodyOK(CContextType context) { 
						// Doing a regular compile on 2nd round so do not allow empty bodies
						if (isSecondRound) return false; 
						return jmlNoBodyOK(context);
					}
				}
		);

	}

	// ----------------------------------------------------------------------
	// RUN FROM COMMAND LINE
	// ----------------------------------------------------------------------

	/** Runs a JML RAC compiler on the command line arguments. */
	public static void main(String[] args) {
		long start_time = System.currentTimeMillis();
		boolean success = compile(args);
		long end_time = System.currentTimeMillis();
		long difference = end_time-start_time;
		if(aRacOptions.verbose()){
			System.err.println("[ compilation time in milliseconds = "+difference+" ]");
			long seconds = TimeUnit.MILLISECONDS.toSeconds(difference);
			System.err.println("[ compilation time i seconds = "+seconds+" ]");
		}
		System.exit(success ? 0 : 1);
	}

	/** Runs a JML RAC compiler on the given arguments. */
	public static boolean compile(String[] args) {
		return new Main().run(parseAspectJOptions(args));
	}

	/**
	 * @param args
	 * @return
	 */
	private static String[] parseAspectJOptions(String[] args) {
		List argList = Arrays.asList(args);
		List argListResult = new ArrayList();
		for (Iterator iterator = argList.iterator(); iterator.hasNext();) {
			String object = (String) iterator.next();
			argListResult.add(object);
		}
		for (Iterator iterator = argList.iterator(); iterator.hasNext();) {
			String arg = (String) iterator.next();
			if(arg.equals("--aspectJCompiler")){
				String argValue = (String) iterator.next();
				ajWeaver = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-aspectJCompiler")){
				String argValue = (String) iterator.next();
				ajWeaver = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--H")){
				String argValue = (String) iterator.next();
				ajWeaver = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-H")){
				String argValue = (String) iterator.next();
				ajWeaver = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--inpath")){
				String argValue = (String) iterator.next();
				inpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-inpath")){
				String argValue = (String) iterator.next();
				inpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--I")){
				String argValue = (String) iterator.next();
				inpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-I")){
				String argValue = (String) iterator.next();
				inpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--outjar")){
				String argValue = (String) iterator.next();
				outjar = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-outjar")){
				String argValue = (String) iterator.next();
				outjar = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--i")){
				String argValue = (String) iterator.next();
				outjar = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-i")){
				String argValue = (String) iterator.next();
				outjar = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-aspectpath")){
				String argValue = (String) iterator.next();
				aspectpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--aspectpath")){
				String argValue = (String) iterator.next();
				aspectpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("--F")){
				String argValue = (String) iterator.next();
				aspectpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
			else if(arg.equals("-F")){
				String argValue = (String) iterator.next();
				aspectpath = argValue;
				argListResult.remove(arg);
				argListResult.remove(argValue);
			}
		}
		String [] result = new String[argListResult.size()];
		int count = 0;

		for (Iterator iterator = argListResult.iterator(); iterator.hasNext();) {
			String object = (String) iterator.next();
			result[count++] = object;
		}
		return result;
	}

	//	----------------------------------------------------------------------
	// Rebelo - RUN ajc FROM COMMAND LINE
	// ----------------------------------------------------------------------

	public void runAjcCompiler() {
		try {
			inform("calling the AspectJ weaver --- ajc");
//			org.aspectj.tools.ajc.Main.main(aRacOptions
//					.generateArgsForAjcCompiler(aRacOptions.destination(),
//							aRacOptions.classpath(), aRacOptions.source(),
//							aRacOptions.inpath(), aRacOptions.outjar(), aRacOptions.aspectpath(), aRacOptions.showWeaveInfo()));
			org.aspectj.tools.ajc.Main ajc = new org.aspectj.tools.ajc.Main();
			org.aspectj.bridge.MessageHandler messageHandler = new org.aspectj.bridge.MessageHandler();
			ajc.run(aRacOptions
					.generateArgsForAjcCompiler(aRacOptions.destination(),
					aRacOptions.classpath(), aRacOptions.source(),
					aRacOptions.inpath(), aRacOptions.outjar(), aRacOptions.aspectpath(), aRacOptions.showWeaveInfo()), messageHandler);
			org.aspectj.bridge.IMessage[] compilerMessages = messageHandler.getMessages(null, true);
			int errors = 0;
			for (int i = 0; i < compilerMessages.length; i++) {
				if(compilerMessages[i].getKind().toString().equals("error")){
					errors++;
				}
				
			}
			for (int i = 0; i < compilerMessages.length; i++) {
				if(compilerMessages[i].getKind().toString().equals("weaveinfo")){
					inform(compilerMessages[i].getMessage());
				}
				else if(compilerMessages[i].getKind().toString().equals("info") && aRacOptions.showWeaveInfo()){
					if(compilerMessages[i].getMessage().startsWith("compiling")){
						inform(compilerMessages[i].getMessage());
					}
				}
				else if(compilerMessages[i].getKind().toString().equals("warning") && aRacOptions.showWeaveInfo()){
					inform(compilerMessages[i].getMessage());
				}
				// compilation errors are always shown --- [[[hemr]]]
				else if(compilerMessages[i].getKind().toString().equals("error")){
					inform(compilerMessages[i].getSourceLocation().getSourceFile().getPath()+":"+compilerMessages[i].getSourceLocation().getLine()+" [error] "+compilerMessages[i].getMessage());
					inform(compilerMessages[i].getSourceLocation().getContext());
				}
			}
			if(errors > 0){
				System.err.println();
				if(errors == 1){
					System.err.println(errors+" error");
				}
				else{
					System.err.println(errors+" errors");
				}
				
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	// ----------------------------------------------------------------------
	// Rebelo - RUN abc FROM COMMAND LINE
	// ----------------------------------------------------------------------

	public void runAbcCompiler() {
		inform("calling the AspectJ weaver --- abc");
		String [] args = aRacOptions.generateArgsForAbcCompiler(
				aRacOptions.destination(), aRacOptions.classpath());
		abc.main.Main abc;
		try {
			abc = new abc.main.Main(args);
			abc.run();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (CompilerAbortedException e) {
			e.printStackTrace();
		} catch (CompilerFailedException e) {
			// there is no need... since the errors are already presented... [[[hemr]]]
		}
		
//		abc.main.Main.main(aRacOptions.generateArgsForAbcCompiler(
//				aRacOptions.destination(), aRacOptions.classpath()));
	}

//	public void runAbcJaCompiler() {
//		inform("calling the AspectJ weaver --- abc");
//		abc.main.Main.main(aRacOptions.generateArgsForAbcJaCompiler(
//				aRacOptions.destination(), aRacOptions.classpath(),
//				aRacOptions.inpath()));
//	}

	public void parsingAspectJGeneratedFiles(List aspectJFilesPath){
		for (Iterator iter = aspectJFilesPath.iterator(); iter.hasNext();) {
			String currentAspectJFilePath = (String) iter.next();
			inform(JmlMessages.PARSING, 
					makeRelative(currentAspectJFilePath,
							System.getProperty("user.dir"),File.separator) );
		}
	}

	// ----------------------------------------------------------------------
	// RUN FROM GUI
	// ----------------------------------------------------------------------

	/**
	 * Entry point for the GUI
	 *
	 * @param   args    the file, package, and directory names
	 * @param   opt     the options for the tool
	 * @param   os      the output stream for the compiler messages
	 */
	public static boolean compile(String[] args, RacOptions opt,
			OutputStream os) {
		return new Main().run(args, opt, os);
	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/** Returns true if this type should be processed in spec mode - that is
        if methods and constructors without bodies are allowed.  This is the
        case if it is the declaration of a class and the file name containing
        the declaration does not end in .java.
	 */
	static public boolean isSpecMode(JmlTypeDeclaration decl) {
		return !decl.hasSourceInRefinement();
//		&& !Main.aRacOptions.noSource();
	}

	/**
	 * Generates the first task in the compilation sequence. This is a
	 * method so subclasses can modify the task sequence.
	 *
	 * <pre><jml>
	 * also
	 *   requires infiles != null && (\forall Object o; infiles.contains(o);
	 *                                  o instanceof String);
	 * </jml></pre>
	 *
	 */
	public ParseTask firstTask( ArrayList infiles ) {
		if (isSecondRound) {
			return new JavaParseTask(infiles);
		} else {
			ArrayList ajFiles = new ArrayList();
    		for (Iterator iterator = infiles.iterator(); iterator.hasNext();) {
    			String currentFile = (String) iterator.next();
    			if(currentFile.endsWith(".aj")){
    				ajFiles.add(currentFile);
    			}
    		}
    		for (Iterator iterator = ajFiles.iterator(); iterator.hasNext();) {
    			String currentAjFile = (String) iterator.next();
    			File ajFile = new File(currentAjFile);
    			infiles.remove(currentAjFile);
    			if(!ajFile.getAbsolutePath().contains("AspectJMLRac")){
    				aRacOptions.addAspectFilePathToCompilation(ajFile.getAbsolutePath());
    			}
    		}
			return new JmlParseTask(infiles);
		}
	}

	/**
	 * Generates the first task in the compilation sequence. This method
	 * returns JML parser if this is the first round; otherwise, this 
	 * method returns Java parser.
	 */
	public ParseTask firstTask(File filename, ExpectedResult expected) {
		if (isSecondRound) {
			return new JavaParseTask(filename, expected);
		} else {
			return new JmlParseTask(filename, expected);
		}
	}

	/** Creates an object to do the parsing of the command line arguments
	 * and to store the values of the flags and options so obtained 
	 * (it does not actually do the argument parsing).  
	 * It is overridden here from mjc.Main so that we can
	 * instantiate a RacOptions object, in order to parse some new
	 * options specific to this compiler (cf. RacOptions.opt).
	 * @see RacOptions */
	protected MjcCommonOptions makeOptionsInstance() {
		aRacOptions = new ARacOptions("ajmlc"); // prefix to error messages
		exposeOptions(aRacOptions);
		//opt.Quiet = true; // enforce quiet mode.
		return aRacOptions;
	}

	/** Assigns opt to the local instance of RacOptions, assigns opt to
	 *  an instance of jmlOptions in the checker, and returns opt as an 
	 *  instance of MjcCommonOptions so it can be assigned to
	 *  the options variable in mjc's Main.  This is done so we can access
	 *  options that are only processed in MjcCommonOptions.
	 */
	//@ also
	//@ requires opt instanceof RacOptions;
	protected MjcCommonOptions getOptionsInstance(MjcCommonOptions opt) {
		aRacOptions = (ARacOptions)opt;
		exposeOptions((ARacOptions)opt);
		return opt;
	}

	/**
	 * Sets the static field, <code>jmlOptions</code>, to the given
	 * arugment so that typechecking routines can access command-line
	 * options.
	 * 
	 * <pre><jml>
	 * also
	 *   assignable jmlOptions;
	 *   ensures jmlOptions == opt;
	 * </jml></pre>
	 */
	protected void exposeOptions(/*@ non_null @*/ JmlCommonOptions opt) {
		super.exposeOptions(opt);
		aRacOptions = (ARacOptions) opt;
	}

	/**
	 * Creates a compilation unit context for this compiler.  
	 *
	 * <pre><jml>
	 * also
	 *   requires cunit != null;
	 *   ensures \result != null && contextsCreated.contains(\result);
	 * </jml></pre>
	 *
	 */
	public CCompilationUnitContextType 
	createCompilationUnitContext( JCompilationUnitType jc, 
			CCompilationUnit cunit ) 
	{
		if (isSecondRound) {
			// MJ compilation unit context for the second round
			// see org.multijava.mjc.Main's definition
			CCompilationUnitContextType result = 
				new CCompilationUnitContext( this, cunit );
			contextsCreated.add(result);
			return result;
		} else {
			// JML compilation unit context for the first round
			return super.createCompilationUnitContext(jc, cunit);
		}
	}

	/**
	 * Adds a class to the list of classes to be generated in
	 * bytecode.  It is overridden here from mjc.Main to ignore model
	 * classes and interfaces, and to work only during the second
	 * round of compilation.
	 *
	 * <pre><jml>
	 * also
	 *   requires clazz != null;
	 *   assignable classes;
	 *   ensures classes.contains(clazz);
	 * </jml></pre>
	 */
	public void classToGenerate(CSourceClass clazz)  {
		// ignore during the first round if not generating symbol files
		if (!isSecondRound && !hasOptionXsymw()) {
			return;
		}

		// ignore a model class during the second round
		if (isSecondRound && 
				((clazz instanceof JmlSourceClass) &&
						((JmlSourceClass)clazz).isEffectivelyModel())) {
			return;
		}

		super.classToGenerate(clazz);
	}

	/** Prepares the second round of compilation by cleaning side-effects 
	 * done by the first round. 
	 */
	protected void prepareSecondRound() {
		if (isSecondRound) {
			return;
		}
		isSecondRound = true;

		// generate symbol tables
		genCode();
		classes.clear();

		// clean Java/JML signature forests and initialize standard
		// Java classes such as Object, Class, String, etc by
		// selecting the Java (mjc) type loader for the second round
		// of compilation
		initSecondSession();

		// turn Quiet on for the second pass
		//((JmlCommonOptions)options).Quiet = true;
	}

	/** Initializes the "class loader" for the second round of
	 * compilation. */
	protected void initSecondSession() {
		initSession( TypeLoader.getSingleton() );
	}

	/**
	 * Returns the next task to be performed after <code>oldTask</code>.
	 * This method uses the dynamic type of <code>oldTask</code> along
	 * with the command line options to determine what task to add to
	 * the task queue after the given task completes. It is overriden
	 * here to add JML RAC specific tasks.
	 *
	 * <pre><jml>
	 * also
	 *   requires oldTask != null;
	 * </jml></pre>
	 */
	protected Task createTaskAfter(Task oldTask) {

		if (oldTask instanceof JmlTypecheckTask) {
			if (!hasOptionXsymw() &&
					canStopSequenceBeforeAllPasses( oldTask )) {
				// For 2nd round, next task should be TranslateMJTask
				return ((RacOptions)options).nowrite() ? null :
					new TranslateMJTask(((TypecheckTask) oldTask).trees(),
							oldTask.sequenceID());
			} else if (hasOptionXsymw()) {
				// Experimental feature to generate symbol (.sym) files;
				// The .sym files don't support checking assignable
				// clauses yet, so the JmlCheckAssignableTask is skipped.
				if(hasOptionXsymw()){
					if(isSecondRound){
						return ((RacOptions)options).nowrite() ? null :
							new TranslateMJTask(((TypecheckTask) oldTask).trees(),
									oldTask.sequenceID());
					}else{
						CompilerPassEnterable[] trees 
						= ((TypecheckTask) oldTask).trees();
						return new TranslateMJTask( trees, 
								oldTask.sequenceID() );                        
					}
				}
			} else {
				CompilerPassEnterable[] trees 
				= ((TypecheckTask) oldTask).trees();
				return new JmlCheckAssignableTask( trees, 
						oldTask.sequenceID() );
			}
		} else if (oldTask instanceof TypecheckTask) {
			if (hasOptionXsymw()) {
				if (isSecondRound) {
					// translate RAC code into Java bytecode
					return ((RacOptions)options).nowrite() ? null :
						new TranslateMJTask(((TypecheckTask) oldTask).trees(),
								oldTask.sequenceID());
				} else {
					// generate symbol files
					return 
					new TranslateMJTask(((TypecheckTask) oldTask).trees(),
							oldTask.sequenceID());
				}                
			} else {
				if (!canStopSequenceBeforeAllPasses(oldTask)) {
					// 1st round and not recursively referenced types,
					// so generate RAC code from AST
					JmlCompilationUnit[] trees = filterOut(
							((TypecheckTask) oldTask).trees());
					return (trees.length > 0) ?
							new JmlGenerateAssertionTask(trees,oldTask.sequenceID())
					: null;
				} else {
					// 2nd round, translate RAC code into Java bytecode
					return ((RacOptions)options).nowrite() ? null :
						new TranslateMJTask(((TypecheckTask) oldTask).trees(),
								oldTask.sequenceID());
				}
			}
		} else if (oldTask instanceof TranslateMJTask) {
			if (canStopSequenceBeforeAllPasses(oldTask)) {
				// 1st round, recursive type and hasOptionXsymw()
				// or 2nd round
				return null;
			} else {
				// 1st round and not recursive type
				JmlCompilationUnit[] trees = filterOut(
						((TranslateMJTask) oldTask).trees());
				return (trees.length > 0) ?
						new JmlGenerateAssertionTask(trees,oldTask.sequenceID())
				: null;                
			}
		} else if (oldTask instanceof JmlGenerateAssertionTask) {
			// pretty print or write RAC code to internal file
			CompilerPassEnterable[] trees =
				((JmlGenerateAssertionTask) oldTask).trees();
			if (((RacOptions)options).print())
				return new JmlPrettyPrintTask(trees, oldTask.sequenceID());
			else
				return new JmlWriteAssertionTask(trees, oldTask.sequenceID());

		} else if (oldTask instanceof JmlWriteAssertionTask) {
			// start the second round of compilation, i.e.,
			// compilation of RAC code
			prepareSecondRound();
			
			if(!((RacOptions)options).nowrite()){
				if(!options.quiet()){
					parsingAspectJGeneratedFiles(aRacOptions.getAspectFilePaths());
				}
				
				if(ajWeaver != null){
					aRacOptions.set_ajWeaver(ajWeaver);
				}
				if(inpath != null){
					aRacOptions.set_inpath(inpath);
				}
				if(outjar != null){
					aRacOptions.set_outjar(outjar);
				}
				//Rebelo - Calling the chosen AspectJ compiler from command line
				if (aRacOptions.ajWeaver().equals("ajc")){
					runAjcCompiler(); // Rebelo - Calling the ajc compiler	
				}
				else if (aRacOptions.ajWeaver().equals("abc")){
					runAbcCompiler(); // Rebelo - Calling the abc compiler
				}
//				else if (aRacOptions.ajWeaver().equals("abc.ja")){
//					runAbcJaCompiler(); // Rebelo - Calling the abc compiler
//				}
				/*else if (aRacOptions.getAspectjCompiler().equals("opt-abc")){
	            	runOptAbcCompiler(); // Rebelo - Calling the abc compiler
	            }*/
				else{
					System.err.println("Chosen AspectJ compiler does not exist!!");	
				} 
			}
			//return firstTask(((JmlWriteAssertionTask)oldTask).racFiles());
		} 

		return super.createTaskAfter(oldTask);
	}


	/** Filter out files that aren't to be processed; we do however keep
        non-.java files, whatever their suffix.
	 */
	/** Filters out non-RACable files. E.g., ".jml" files. */
	private static JmlCompilationUnit[] filterOut(
			CompilerPassEnterable[] trees) {
		java.util.ArrayList racables = new java.util.ArrayList(trees.length);
		for (int i = 0; i < trees.length; i++) {
			if ((trees[i] instanceof JmlCompilationUnit)) {
				//String path = ((JmlCompilationUnit)trees[i]).file().getPath();
				JmlCompilationUnit currentCunit = (JmlCompilationUnit)trees[i];
				currentCunit.combinedTypeDeclarations();
				racables.add(trees[i]);

			}
		}
		return (JmlCompilationUnit[]) racables.toArray(
				new JmlCompilationUnit[racables.size()]);
	}

	// -------------------------------------------------------------
	// NESTED CLASSES
	// -------------------------------------------------------------

	/**
	 * A parser class for the seconding round compilation. We use
	 * a modified version of MJC parser (instead of the JML parser)
	 * for the second round compilation. This class parses a group 
	 * of files, given by filenames as strings, and generates 
	 * a forest of ASTs. */
	public class JavaParseTask extends ParseTask {
		public JavaParseTask(ArrayList infiles) {
			super(infiles);
		}

		public JavaParseTask(File fileName, ExpectedResult expected) {
			super(fileName, expected);
		}

		/**
		 * Parses the given file and returns an AST representing it.
		 *
		 * @param       file    the file to be parsed
		 * @return      the compilation unit defined by this file
		 *
		 * <pre><jml>
		 * also
		 *   requires file!=null && file.exists();
		 * </jml></pre>
		 */
		protected JCompilationUnitType parseFile(File file) {
			if (!((JmlCommonOptions)options).Quiet()) {
				inform(JmlMessages.PARSING, 
						makeRelative(file.toString(),
								System.getProperty("user.dir"),File.separator) );
			}

			File apparentFile = null;
			if (racFileMap.containsKey(file)) {
				apparentFile = (File) racFileMap.get(file);
				// register that the apparentFile has already been
				// processed, note that the inherited execute() method
				// registers that file has already been processed
				successfullyParsed(apparentFile);
			} else {
				apparentFile = file;
			}

			Reader buffer = null;
			try {
				buffer = new BufferedReader(new FileReader(file));
			} catch (IOException e) {
				reportTrouble(e);
				return null;
			}

			MjcLexer mjLexer;
			JavadocLexer docLexer;
			MjcParser parser = null; 
			JCompilationUnitType unit;

			// Used to switch lexers.  Aliases are created within the
			// lexer instances.
			ParsingController parsingController;

			Long duration = null;
			long lastTime = System.currentTimeMillis();


			// WMD
			// The jmlrac generated code does not follow the Universe
			// type system yet, but to enable runtime checks of
			// Universe casts also in JMLRac, we found the following
			// solution:
			// The Universe modifiers are written to the
			// JMLRac-generated source (by MjcPrettyPrinter). In the
			// second pass, we parse the Universe keywords, but do not
			// typecheck the code. Then at code generation we create
			// the bytecode for the runtime checks.
			// The Universe type rules are already checked in the
			// first pass, so this solution should be sound for the
			// user code.
			allowUniverseChecks = false;


			parsingController = new ParsingController( buffer, apparentFile );
			mjLexer = new MjcLexer( parsingController, 
					options.source().equals("1.4"),
					options.multijava(),
					allowUniverseKeywords, // WMD
					Main.this );
			docLexer = new JavadocLexer( parsingController );

			try {
				parsingController.addInputStream( mjLexer, "multijava" );
				parsingController.addInputStream( docLexer, "javadoc" );
				parsingController.selectInitial( "multijava" );
				if (!parseJavadoc) {
					parsingController.discardAllTokensFor("javadoc");
				}
				parser = new MjcParser(Main.this, 
						parsingController.initialOutputStream(),
						parsingController,
						options.generic(),
						options.multijava(), 
						options.relaxed(), 
						allowUniverseKeywords, // WMD
						parseJavadoc );

				unit = parser.jCompilationUnit();
				unit.cachePassParameters(Main.this, destination);
			} catch (ParsingController.ConfigurationException e) {
				reportTrouble (
						new FormattedException(
								MjcMessages.PARSER_INITIALIZATION_PROBLEM,
								apparentFile.getName(), e.getMessage()));
				unit = null;
			} catch (antlr.ANTLRException e) {
				reportTrouble(parser.beautifyParserError(e));
				unit = null;
			} catch (Exception e) {
				reportTrouble(e);
				e.printStackTrace();
				unit = null;
			} finally {
				duration = new Long(System.currentTimeMillis() - lastTime);
				try {
					buffer.close();
				} catch(IOException e) {
					reportTrouble(e);
				}
			}

			if(verboseMode()) {
				inform(CompilerMessages.FILE_PARSED, apparentFile.getPath(), 
						duration);
			}

			return unit;
		}
	}

	///////////////////////////////////////////////////////////////////////
	// RAC-specific tasks                                                //
	///////////////////////////////////////////////////////////////////////

	/**
	 * @param file
	 * @return
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private boolean isGeneratableCode(File file)
	throws FileNotFoundException, IOException {
		boolean isGeneratableCode = false;
		FileInputStream   fileInputStream = new FileInputStream(file);  
		InputStreamReader inputStreamReader = new InputStreamReader(fileInputStream);  
		LineNumberReader  lineNumberReader= new LineNumberReader(inputStreamReader);  
		String linha;  
		while(lineNumberReader.ready()) {  
			linha = lineNumberReader.readLine();  
			if(linha.contains("Generated by AspectJML to")){
				isGeneratableCode = true;
				break;
			}
		}
		return isGeneratableCode;
	}
	
	private boolean isGeneratableCodeForStringFile(String fileAsString)
			throws FileNotFoundException, IOException {
		boolean isGeneratableCode = false;
		
		BufferedReader buffer = new BufferedReader(new StringReader(fileAsString));
		String line = buffer.readLine();
		while (line != null) {
			// if any
			if(line.contains("Generated by AspectJML to")){
				isGeneratableCode = true;
				break;
			}
			line = buffer.readLine();
		}
		buffer.close();
		return isGeneratableCode;
	}

	/**
	 * A task class for pretty-printing the trees in the AST forest.  
	 */
	public class JmlPrettyPrintTask extends PrettyPrintTask {
		/**
		 * Constructs a task for pretty printer the trees in the given
		 * forest.  Stores an alias to trees.  */
		public JmlPrettyPrintTask( CompilerPassEnterable[] trees,
				Object sequenceID ) {
			super( trees, sequenceID );
		}

		/**
		 * Generate the source code of parsed compilation unit
		 * @param tree the compilation unit
		 */
		protected void processTree( CompilerPassEnterable tree ) {
			// tree can be an anonymous or local inner class.
			if (tree == null || !(tree instanceof JmlCompilationUnit))
				return;

			// the .aj file
			File file = null;
			// the target directory taking care of -d option
			String destDir = "";
			if(aRacOptions.destination() == null){
				destDir = ((JmlCompilationUnit) tree).packageNameAsString();
			}
			File targetDir = 
				destination.classFileTargetDirectory(
						destDir,
						((JmlCompilationUnit) tree).file());
			try { 				
				final JmlCompilationUnit cunit = (JmlCompilationUnit) tree;
				StringWriter sw = new StringWriter();
				prettyPrintStr(sw, cunit);
				String fileAsString = sw.toString();
				boolean isGeneratableCode = isGeneratableCodeForStringFile(fileAsString);
				if(isGeneratableCode){
					String packageName = ((JmlCompilationUnit) tree).packageNameAsString().replace("/", "_");
					file = new File(targetDir,
							RacConstants.TN_TEMPORARY_ASPECT_FILE_NAME+packageName+((JmlCompilationUnit) tree).fileNameIdent()+".aj");
					prettyPrint(file, cunit);
				}
			} catch (IOException e) {
				reportTrouble(e);
//				System.err.println("Can't create or write to file " + 
//						Utils.relativePathTo(file) + "!");
				noteError();
			}
		}

		/** Pretty-print the AST tree to the given file */
		private void prettyPrint(File file, JmlCompilationUnit tree) {
			RacPrettyPrinter pp;
			pp = new RacPrettyPrinter(file,(JmlModifier)modUtil);
			tree.accept(pp);
			pp.close();
		}
		
		private void prettyPrintStr(StringWriter fileStrWriter, JmlCompilationUnit tree) {
			RacPrettyPrinter pp;
			pp = new RacPrettyPrinter(fileStrWriter,(JmlModifier)modUtil);
			tree.accept(pp);
			pp.close();
		}
	}

	/**
	 * A task class for generating RAC code. The instrumented code is
	 * stored to a temporary file and further processed to generate
	 * bytecode by the following tasks.
	 */
	public class JmlWriteAssertionTask extends JmlPrettyPrintTask {
		public JmlWriteAssertionTask( CompilerPassEnterable[] trees,
				Object sequenceID ) {
			super( trees, sequenceID );
			aRacFiles = new ArrayList();
		}

		protected void processTree( CompilerPassEnterable tree ) {
			
			// this option disable the RAC code generation.
			if(((RacOptions)options).nowrite()){
				return;
			}
			
			// tree can be an anonymous or local inner class.
			if (tree == null || !(tree instanceof JmlCompilationUnit))
				return;
			try {
				String packageName = ((JmlCompilationUnit) tree).packageNameAsString().replace("/", "_");
				final JmlCompilationUnit cunit = (JmlCompilationUnit) tree;
				final String fileName = RacConstants.TN_TEMPORARY_ASPECT_FILE_NAME+packageName+((JmlCompilationUnit) tree).fileNameIdent()+".aj";
				final String filePath = (cunit.getFilePath().endsWith(".java")? cunit.getFilePath().replace(cunit.fileNameIdent()+".java", "") : cunit.getFilePath().replace(cunit.fileNameIdent()+".jml", ""));
				final String currentAspectFilePath = filePath+fileName;
				//File tmpFile = File.createTempFile("jmlrac", ".java");
				File tmpFile = new File(filePath+fileName);
				tmpFile.deleteOnExit();
				prettyPrint(tmpFile, cunit);

				// verifying if there is generatable code
				boolean isGeneratableCode = isGeneratableCode(tmpFile);  
				if(isGeneratableCode){
					if(!cunit.getFilePath().endsWith(".jml")){
						File tmpFile2 = new File(cunit.getFilePath());

						// verifying is a source file exists
						if(tmpFile2.exists()){
							aRacOptions.addJavaFilePathToCompilation(cunit.getFilePath());
							aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath);
						}
						else if(aRacOptions.sourcepath() == null){
							aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath);
						}
						else{
							File sourcepath = new File(aRacOptions.sourcepath());
							if((sourcepath.isDirectory()) && ((new File(sourcepath.getPath()+"\\"+cunit.fileNameIdent()+".java")).exists())){
								aRacOptions.addJavaFilePathToCompilation(sourcepath.getPath()+"\\"+cunit.fileNameIdent()+".java");
								aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath);
							}
							else if((sourcepath.isFile()) && (sourcepath.getPath().endsWith(cunit.fileNameIdent()+".java"))){
								aRacOptions.addJavaFilePathToCompilation(sourcepath.getPath());
								aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath);
							}
							else{
								aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath);
							}
						}
					}
					// is .jml file
					else{
						File tmpFile2 = new File(cunit.getFilePath().replace(".jml", ".java"));
						if(tmpFile2.exists()){
							aRacOptions.addJavaFilePathToCompilation(cunit.getFilePath().replace(".jml", ".java"));
						}
						else if(aRacOptions.sourcepath() != null){
							File sourcepath = new File(aRacOptions.sourcepath());
							if((sourcepath.isDirectory()) && ((new File(sourcepath.getPath()+"\\"+cunit.fileNameIdent()+".java")).exists())){
								aRacOptions.addJavaFilePathToCompilation(sourcepath.getPath()+"\\"+cunit.fileNameIdent()+".java");
							}
							else if((sourcepath.isFile()) && (sourcepath.getPath().endsWith(cunit.fileNameIdent()+".java"))){
								aRacOptions.addJavaFilePathToCompilation(sourcepath.getPath());
							}
						}
						aRacOptions.addAspectFilePathToCompilation(currentAspectFilePath, fileName);
					}
				}
				else{
					if(cunit.getFilePath().endsWith(".java")){
						aRacOptions.addJavaFilePathToCompilation(cunit.getFilePath());	
					}
					else if(cunit.getFilePath().endsWith(".jml")){
						File tmpFile2 = new File(cunit.getFilePath().replace(".jml", ".java"));
						if(tmpFile2.exists()){
							aRacOptions.addJavaFilePathToCompilation(cunit.getFilePath().replace(".jml", ".java"));
						}	
					}
				}
			}
			catch (IOException e) {
				reportTrouble(e);
			}
		}

		public ArrayList racFiles() {
			return aRacFiles;
		}

		/** Pretty-print the AST tree to the external file */
		private void prettyPrint(File file, JmlCompilationUnit tree) {
			RacPrettyPrinter pp = 
				new RacPrettyPrinter(file, (JmlModifier)modUtil);
			tree.accept(pp);
			pp.close();        
		}

		/** temp rac files to be compiled by the next task */
		private ArrayList aRacFiles;
	}



	/**
	 * A task for generating runtime assertion checker (RAC) code. 
	 * The class is constructed on an AST forest.  
	 */
	public class JmlGenerateAssertionTask extends TreeProcessingTask
	implements RacConstants {

		/**
		 * Constructs a task for generating runtime assertion code
		 * for the classes in the given. Mutates the trees.  */
		public JmlGenerateAssertionTask( CompilerPassEnterable[] trees,
				Object sequenceID ) {
			super( PRI_GENERATE_ASSERTION, sequenceID, trees,
					RacMessages.RAC_GEN );

			// filter out non-instrumentable entries, i.e., those already
			// instrumented.
			ArrayList l = new ArrayList(trees.length);
			for (int i = 0; i < trees.length; i++) {
				if (trees[i] == null || 
						!(trees[i] instanceof JmlCompilationUnit)) {
					continue;
				}

				JmlCompilationUnit cunit = (JmlCompilationUnit) this.trees[i];

				// is refined by another cunit?
				if (cunit.isRefined()) {
					continue;
				}

				// should cunit be silently skipped, e.g., jmlunit gen files.
				if (shouldBeSkipped(cunit)) {
					continue;
				}

				// is already instrumented?
				if (isInstrumented(cunit)) {
					System.err.println("Can't compile jmlc-generated file " + 
							Utils.relativePathTo(cunit.file()) + 
					"!");
					noteError();
				} else {
					l.add(this.trees[i]);
				}
			}
			this.trees = (CompilerPassEnterable[]) 
			l.toArray(new CompilerPassEnterable[l.size()]);
		}

		/** Processes the given tree, <code>tree</code>. I.e.,
		 * mutates the AST to turn it into an instrumented Java
		 * source file. */
		protected void processTree(CompilerPassEnterable tree) {
			//@ assume tree != null && tree instanceof JmlCompilationUnit;
			final JmlRacGenerator racgen 
			= createRacGenerator(aRacOptions, Main.this);
			((JmlCompilationUnit)tree).accept(racgen);
		}

		/** Returns true if the given compilation unit,
		 * <code>cunit</code>, is for a jmlc-generated Java source
		 * file.
		 *
		 * <pre><jml>
		 * requires cunit != null;
		 * </jml></pre>
		 */
		private boolean isInstrumented(JmlCompilationUnit cunit) {
			JTypeDeclarationType[] tdecls = cunit.typeDeclarations();
			for (int i = 0; i < tdecls.length; i++) {
				JFieldDeclarationType[] fields = tdecls[i].fields();
				for (int j = 0; j < fields.length; j++) {
					if (VN_RAC_COMPILED.equals(fields[j].ident()))
						return true;
				}
			}
			return false;
		}

		/** Returns true if the given compilation unit,
		 * <code>cunit</code>, should be skipped. E.g., jmlunit
		 * generated files are not jmlc compiled.
		 *
		 * <pre><jml>
		 * requires cunit != null;
		 * </jml></pre>
		 */
		private boolean shouldBeSkipped(JmlCompilationUnit cunit) {
			String name = cunit.fileNameIdent();
			return name.endsWith(TN_JMLUNIT_TEST_POSTFIX) ||
			name.endsWith(TN_JMLUNIT_TESTDATA_POSTFIX);
		}
	}

	protected JmlRacGenerator createRacGenerator(
			RacOptions opt, Main main) {
		return new JmlRacGenerator(opt, main);
	}

	// -------------------------------------------------------------
	// DATA MEMBERS
	// -------------------------------------------------------------

	/** Task priorities for tasks defined in this class. */
	public final static int PRI_GENERATE_ASSERTION = 550;
	public final static int PRI_GENERATE_SYMBOL = 450;

	/** Map from temp RAC file names to their original file names */
	private java.util.Map racFileMap = new java.util.HashMap();

	/** Accessor method to racFileMap. This is used by the wrappers
	 *   Main class to compile all the generated files.
	 **/ 
	protected java.util.Map getFileMap() {
		return racFileMap;
	}

	protected void setFileMap(java.util.Map map) {
		racFileMap = map;
	}

	/** Default modifier utility to use. */
	public final static ModifierUtility modUtil = new JmlModifier();

	/** Indicates whether we are in the first or second round of
	 * compilation. */
	protected boolean isSecondRound = false;

	/** Command-line options.
	 *
	 * <pre><jml>
	 * invariant racOptions == options;
	 * </jml></pre>
	 */
	public static ARacOptions aRacOptions;

	public static String ajWeaver;
	public static String inpath;
	public static String outjar;
	public static String aspectpath;

}
