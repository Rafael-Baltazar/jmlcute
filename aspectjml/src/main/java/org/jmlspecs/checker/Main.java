/*
 * Copyright (C) 2000-2004 Iowa State University
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
 * $Id: Main.java,v 1.87 2006/11/28 20:06:36 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.util.QDoxUtil;
import org.jmlspecs.util.classfile.JmlAttributeParser;
import org.multijava.mjc.CCompilationUnit;
import org.multijava.mjc.CCompilationUnitContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CModifier;
import org.multijava.mjc.CSourceClass;
import org.multijava.mjc.CompilerPassEnterable;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.MjcCommonOptions;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.ParsingController;
import org.multijava.util.FormattedException;
import org.multijava.util.Utils;
import org.multijava.util.classfile.AttributeList;
import org.multijava.util.compiler.CompilationAbortedException;
import org.multijava.util.compiler.CompilerMessages;
import org.multijava.util.compiler.ModifierUtility;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.WarningFilter;

/**
 * This class implements the entry point of the JML compiler.  Use
 * <code>java org.jmlspecs.checker.Main --help</code> to get usage
 * options.  */
public class Main extends org.multijava.mjc.Main {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /** The principal constructor for an object to do the work of the
        Jml compiler.*/
    public Main() {
        // Use the mjc compiler, but give it an expanded list of
        // access keywords.
        this( new CModifier( Constants.ACCESS_FLAG_ARRAY,
                              Constants.ACCESS_FLAG_NAMES ) );
    }

    protected boolean jmlNoBodyOK(CContextType context) {
	CCompilationUnitContextType c = context.getCompilationUnit();
	if (!(c instanceof JmlCompilationUnitContext)) return false;
	Main.PTMode m = ((JmlCompilationUnitContext)c).mode();
	return (m == Main.SPEC_MODE || m == Main.JML_MODE );
    }


    
    /** Construct a JML compiler (an object of <code>Main</code>) that
     * uses the given <code>ModifierUtility</code>. This constructor
     * allows the subclasses to have their owen version of modifier 
     * utilities.
     */
    protected Main( ModifierUtility modUtil ) {
        super( modUtil );

        appName = "jml";
        // Also enable the parsing of javadoc comments, both so that
        // we can print out javadoc with jml annotations and so that
        // we can get the jml stuff inside of javadoc comments.
        parseJavadoc = true;

        setContextBehavior(
            new ContextBehavior() {
                public boolean noBodyOK(CContextType context) {
		    return jmlNoBodyOK(context);
                }
            }
        );

    }

    // ----------------------------------------------------------------------
    // RUN FROM COMMAND LINE
    // ----------------------------------------------------------------------

    /**
     * The entry point when starting this program from the command line.
     *
     * @param   args            the command line arguments
     */
    public static void main(String[] args) {

        boolean success;

        success = compile(args);
//	if (jmlOptions.nonnull()) NonNullStatistics.outPutStat();
	/* removed to disable cache
        JmlFileFinder.dumpNotFoundHashSet();
	*/
        System.exit(success ? 0 : 1);
    }

    /**
     * Second entry point.  This function is overridden from mjc.Main
     * so that we can * instantiate a derived class Main object.  */
    public static boolean compile(String[] args) {
        return new Main().run(args);
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
    public static boolean compile(String[] args, JmlOptions opt, 
                                  OutputStream os) {
        return new Main().run(args, opt, os);
    }
        
    // ----------------------------------------------------------------------
    // METHODS FOR BOTH COMMAND LINE AND GUI
    // ----------------------------------------------------------------------
    
    /** Initializes the "class loader" for this compilation session. */
    protected void initSession() {
        initSession( JmlTypeLoader.getJmlSingleton() );
    }

    // Parsing and typechecking modes

    static class PTMode {
        static public PTMode mode(String s) {
         return (s.endsWith(".java") ? JAVA_MODE : // .java
                    s.endsWith("spec") ? SPEC_MODE :  // .spec or .refines-spec
                    s.endsWith("-java") ? SPEC_MODE : // .refines-java
                    s.endsWith("jml") ? JML_MODE :    // .jml or .refines-jml
                    s.endsWith(".java-refined") ? SPEC_MODE :
                    s.endsWith(".spec-refined") ? SPEC_MODE :
                    s.endsWith(".jml-refined") ? JML_MODE :
                    null);
        }
    }
    static final PTMode JAVA_MODE = new PTMode();
    static final PTMode SPEC_MODE = new PTMode();
    static final PTMode JML_MODE = new PTMode();

    /** This function creates an object to do the parsing of the
     *  command line arguments and to store the values of the flags
     *  and options so obtained (it does not actually do the argument
     *  parsing).  It is overridden here from mjc.Main so that we can
     *  instantiate a JmlOptions object, in order to parse some new
     *  options specific to this compiler (cf. JmlOptions.opt).
     *  @see JmlOptions */
    protected MjcCommonOptions makeOptionsInstance() {
        JmlOptions opt = new JmlOptions("aspectjml"); // prefix to error messages
        exposeOptions(opt);
        //opt.Quiet = true; // enforce quiet mode.
        return opt;
    }

    /** Assigns opt to the local instance of JmlCommonOptions and returns
     *  opt as an instance of MjcCommonOptions so it can be assigned to
     *  the options variable in mjc's Main.  This is done so we can access
     *  options that are only processed in MjcCommonOptions.
     */
    //@ also
    //@ requires opt instanceof JmlOptions;
    protected MjcCommonOptions getOptionsInstance(MjcCommonOptions opt) {
        exposeOptions((JmlOptions)opt);
        return opt;
    }
    
    /**
     * Sets the static field, <code>jmlOptions</code>, to the given
     * arugment so that typechecking routines can access command-line
     * options.
     * 
     * <pre><jml>
     * assignable jmlOptions;
     * ensures jmlOptions == opt;
     * </jml></pre>
     */
    protected void exposeOptions(/*@ non_null @*/ JmlCommonOptions opt) {
        jmlOptions = opt;
    }

    /**
     * Parses the argument list.  Mutates infiles, options.  Returns true
     * if there were no problems parsing the arguments.  The list of
     * command line arguments is parsed per the options defined in
     * JmlOptions.opt.  Values of given options are stored in the protected
     * variable super.options.  Remaining command-line arguments are
     * considered to be filenames or directories.  Any directories are
     * expanded to be all the *.java files in the directory (recursively
     * including *.java files in subdirectories if the --recursive flag
     * is set).  The resulting list of files to be processed is stored in
     * the ArrayList infiles.
     */
    //@ also
    //@    requires args != null && infiles != null;
    //@    modifies options;
    //@   modifies (* the object that is referenced by infiles *);
    //@    ensures options instanceof JmlOptions;
    /*@    ensures (* values set in the fields of options
      @               correspond to the contents of args *);
      @    ensures (* items in infiles are non-null Strings
      @              corresponding to files that exist
      @              and were on the command line *);
      @    ensures (* \result is true if arguments parsed successfully *);
      @*/
    public boolean parseArguments(String[] args, ArrayList infiles) {
        // No special parsing required, so we simply use the super
        // class parser, which leaves in 'infiles' all non-option
        // command-line arguments.
        if (! super.parseArguments(args, infiles)) return false;

        // Take care of some interactions among options

        // Turn Quiet off if verbose is on

        if (options.verbose()) ((JmlCommonOptions)options).set_Quiet(false);

        // Turn quiet on if Quiet is on

        if (((JmlCommonOptions)options).Quiet()) options.set_quiet(true);

        return true;
    }

    /** This class is used with the Directory.list method to list
        those files in a directory that this program is interested in
        processing - in this case, all those that end in '.java', '.jml'
        or '.spec'.  */
    // This should be private, but javadoc does not then list its
    // innards.  !FIXME! - DRCok
    static class Filter implements FilenameFilter {
        private static String[] suffixes
            = {".refines-java", ".refines-spec", ".refines-jml",
               ".java", ".spec", ".jml"
            };
        
        public Filter() {}

        /*@ also
          @   requires dir != null && name != null 
          @         && (* dir is a Directory, and name is an object in dir *);
          @*/
        public boolean accept(File dir, String name) {
            int p = name.lastIndexOf('.');
            if (p == -1) return false;
            String prefix = name.substring(0,p);
            String suffix = name.substring(p);
            
            for (int i=0; i<suffixes.length; ++i) {
                if (!suffixes[i].equals(suffix)) continue;
                for (int j=0; j<i; j++) {
                    if ((new File(dir,prefix+suffixes[j])).exists()) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        }
    }



    // ----------------------------------------------------------------------


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
    /* Note: This method is called approximately once per file and
           per compilation task.  It would be much more elegant to
           determine the PTMode at the time parsing is initiated (it
           could be passed into the call of jCompilationUnit), and
           stored as part of a JmlCompilationUnit; then we could avoid
           the string matching that happens each time in this routine.
           However, there seemed to be no way to carry the mode
           information (which is just pertinent to jml and not mjc)
           from the initial JmlCompilationUnit to the
           JmlCompilationUnitContext created here, since several
           intermediate steps take place via delegated methods and
           objects in mjc (at least without infecting mjc with
           jml-specific stuff).  Hence we do this here.  Doesn't seem
           to be a particular performance hit.  - David Cok 2/23/2002
        */
    public CCompilationUnitContextType 
        createCompilationUnitContext( JCompilationUnitType jc, 
                                      CCompilationUnit cunit ) 
    {
        JmlCompilationUnitContext jcc = 
            new JmlCompilationUnitContext( this, cunit );
        String s = jc.file().getName();
        PTMode m = PTMode.mode(s);
        jcc.setMode(m);
        CCompilationUnitContextType result = jcc;
        contextsCreated.add(result);
        return result;
    }

    /*
     */
    public static boolean isSpecOrJmlMode(TokenReference t) {
        String s = t.file().getName();
        PTMode m = PTMode.mode(s);
        return m == SPEC_MODE || m == JML_MODE;
    }

    /**
     * Generates the first task in the compilation sequence.  This is a 
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
        return new JmlParseTask( infiles );
    }


    /**
     * Generates the first task in the compilation sequence.  This is
     * a method so subclasses can modify the task sequence.
     */
    public ParseTask firstTask( File filename, ExpectedResult expected ) {
        return new JmlParseTask( filename, expected );
    }

    // ----------------------------------------------------------------------
    // PROTECTED METHODS
    // ----------------------------------------------------------------------

    protected String getWarningFilterNameFromOptions(MjcCommonOptions opts)
    {
        return ((JmlCommonOptions)opts).filter();
    }

    /**
     * Return an instance of the JML default warning filter. */
    protected WarningFilter getDefaultFilter() {
        return new JMLDefaultWarningFilter();
    }

    protected FilenameFilter filenameFilter() {
        try {
            return new AndNotPatternFilenameFilter(new Filter(),
                                                   ((JmlCommonOptions)options)
                                                   .excludefiles());
        } catch (PatternSyntaxException e) {
            reportTrouble(new FormattedException(JmlMessages.INVALID_EXCLUDEFILES_PATTERN_SYNTAX,
                                                 e.getMessage()));
            return new Filter();
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
        if ((clazz instanceof JmlSourceClass) &&
            ((JmlSourceClass)clazz).isRefined()) {
            return;
        }
        super.classToGenerate(clazz);
    }

    // -------------------------------------------------------------
    // TASK AND TASK SEQUENCING CODE
    // -------------------------------------------------------------

    /** 
     * This method returns true iff the file f was specified on the 
     * command line.
     */
    public boolean isCommandLineFile( File f ) {
        String key = Utils.getFilePath( f );
        return commandLineFiles.contains( key );
    }

    /** 
     * This version of catchUp reactivates the given task.
     * TaskQueue passes as far as other files have been processed.
     *
     * <pre><jml>
     * requires task != null;
     * </jml></pre>
     */
    public void catchUpTask( Task task ) {
        taskQueue.add( super.createTaskAfter(task) );
        processTaskQueue();
    }

    /**
     * Parses a file and returns the AST.
     *
     * <pre><jml>
     * requires file != null;
     * </jml></pre>
     *
     */
    public JCompilationUnitType catchUpRefinedFile(File file) {
        //  System.out.println("refine file catch up:"+file.getName());
        if (hasAlreadySuccessfullyParsed(file)) {
            // System.out.println("already processed:"+file.getName());
            JCompilationUnitType refinedAST 
                = JmlTypeLoader.getJmlSingleton().getCUnitAST(file);
            return refinedAST;
        }

        // true means that this is a refined compilation unit.
        JmlParseTask parseTask = 
            new JmlParseTask( file, true, ExpectedIndifferent.instance() );
        taskQueue.add( parseTask );
        processTaskQueue();
        
        // get the AST out of the parse task
        if ( parseTask.trees().length > 0 ) {
            // return the AST so it can be placed in the node for the 
            // refine clause 
            return (JCompilationUnitType) parseTask.trees()[0];
        } else {
            return null;
        }
    }


    /**
     * Returns true if it is OK to abort processing of the given task
     * before it has been processed through all compilation passes.  */
    protected boolean canStopSequenceBeforeAllPasses( Task oldTask ) {
        Object otsi = oldTask.sequenceID();
        return otsi != mainSequenceID();
    }

    /**
     * This method uses the dynamic type of <code>oldTask</code> along
     * with the command line options to determine what task to add to
     * the task queue after the given task completes.  
     *
     * <pre><jml>
     * also
     *   requires oldTask != null && oldTask.completed;
     *   ensures \result == null || 
     *           (\result.sequenceID() == oldTask.sequenceID());
     * </jml></pre>
     *
     */
    protected Task createTaskAfter( Task oldTask ) {
        if (oldTask instanceof CheckInitializerTask) {
            // if this is a "catch up" task for a recursively referenced
            // class, suspend (i.e., may be no need to typecheck it).
            if (!hasOptionXsymw() &&
                canStopSequenceBeforeAllPasses( oldTask )) {

		// Always preprocess C.U.'s for a type referenced by 
		// one of the types being checked.  However, 
		// only continue processing the task if 
		// the symbol table is needed during type checking.

                CompilerPassEnterable[] trees 
                    = ((CheckInitializerTask) oldTask).trees();
                JmlCompilationUnit cUnit;
                for (int i=0; i<trees.length; i++) {
                    if (trees[i] instanceof JmlCompilationUnit) {
                        cUnit = (JmlCompilationUnit) trees[i];
                        String filePath = cUnit.getFilePath();
                        cUnit.setSuspendedTask(oldTask);
                        JmlTypeLoader.getJmlSingleton()
                            .savePartiallyProcessedTask(cUnit);
                        // System.out.println("stop:"+filePath);
                        return null;
                    }
                }
                return super.createTaskAfter( oldTask );
            } else {
                return super.createTaskAfter( oldTask );
            }
        } else if (oldTask instanceof ResolveTopMethodTask) {
            CompilerPassEnterable[] combinedASTs
                = includeAllRefinedCUnits( ((ResolveTopMethodTask)oldTask)
                                           .trees());
            return new JmlTypecheckTask( combinedASTs, oldTask.sequenceID() );
        } else if (oldTask instanceof JmlTypecheckTask) {
            if (!hasOptionXsymw() &&
                canStopSequenceBeforeAllPasses( oldTask )) {
                return null;
            } else if (hasOptionXsymw()) {
                // Experimental feature to generate symbol (.sym) files;
                // The .sym files don't support checking assignable
                // clauses yet, so the JmlCheckAssignableTask is skipped.
                CompilerPassEnterable[] trees 
                    = ((TypecheckTask) oldTask).trees();
                return new TranslateMJTask( trees, 
                                                   oldTask.sequenceID() );
            } else {
                CompilerPassEnterable[] trees 
                    = ((TypecheckTask) oldTask).trees();
                return new JmlCheckAssignableTask( trees, 
                                                   oldTask.sequenceID() );
            }
        } else {
            return super.createTaskAfter( oldTask );
        }
    }

    /**
     * Initialize the compiler (read classpath, initialize type descriptors)
     */
    protected void initialize() {
        super.initialize();
        AttributeList.addParser(new JmlAttributeParser());
    }


    protected CompilerPassEnterable[]
        includeAllRefinedCUnits( CompilerPassEnterable[] trees ) 
    {
        ArrayList allASTs = new ArrayList(trees.length);
        JmlCompilationUnit cUnit;
        for (int i=0; i<trees.length; i++) {
            if (trees[i] instanceof JmlCompilationUnit) {
                cUnit = (JmlCompilationUnit) trees[i];
                String filePath = cUnit.getFilePath();
                if ( ! refinedFileSequenceSet.contains( filePath ) ) {
                    // add all the ASTs in the refinement sequence
                    while (cUnit.refinedCUnit() != null) {
                        cUnit = cUnit.refinedCUnit();
                    }
                    while (cUnit != null) {
                        allASTs.add(cUnit);
                        filePath = cUnit.getFilePath();
                        refinedFileSequenceSet.add( filePath );
                        cUnit = cUnit.refiningCUnit();
                    }
                }
            } else {
                allASTs.add(trees[i]);
            }
        }
        CompilerPassEnterable[] combinedASTs
            = (CompilerPassEnterable[])allASTs.toArray( 
                           new CompilerPassEnterable[allASTs.size()]);
        
        return combinedASTs;
    }

    // -------------------------------------------------------------
    // NESTED CLASSES
    // -------------------------------------------------------------

    /**
     * This class parses a group of files, given by filenames as
     * strings, and generates a forest of ASTs.  */
    public class JmlParseTask extends ParseTask {

        private boolean isRefinedCUnit = false;

        public JmlParseTask( ArrayList infiles ) {
            super( infiles );

//	    if (jmlOptions.nonnull()){
//                NonNullStatistics nn = new NonNullStatistics(files);
//            }

            for (int i=0; i<files.length; i++) {
                String key = Utils.getFilePath( files[i] );
                commandLineFiles.add( key );
            }
        }

        public JmlParseTask( File fileName, ExpectedResult expected ) {
            super( fileName, expected );
        }

        /**
         * Constructs a new parse task for a refined file.  The
         * boolean flag indicates that this is a refined compilation
         * unit.  That information is passed to the parser and is used
         * to control how the types defined in the file are registered
         * in the environment.
         */
        public JmlParseTask( File fileName, boolean isRefinedCUnit,
                             ExpectedResult expected ) {
            super( fileName, expected );
            this.isRefinedCUnit = isRefinedCUnit;
        }

        /**
         * Parses the given file and returns an AST representing it.
         *
         * @param       file    the file to be parsed
         * @return      the compilation unit defined by this file, or
         *                      null if there was an error reading the file
         *
         * <pre><jml>
         * also
         *   requires file!=null && file.exists();
         * </jml></pre>
         *
         */
        protected JCompilationUnitType parseFile(File file) {

        	if (!((JmlCommonOptions)options).Quiet()) {
        		inform(JmlMessages.PARSING, makeRelative(file.toString(),System.getProperty("user.dir"),File.separator) );
        	}


        	// The following is duplicated from the super class.  It
        	// is modified just to provide lexers and parsers that
        	// understand JML syntax.

			BufferedReader buffer = null;
			String fileAsString = "";
			
			boolean java5OrLater = Float.parseFloat(((JmlCommonOptions) options).source()) > 1.4;
			if(java5OrLater){
				// making this true when using source 1.5 or later - [[[hemr]]]
				((JmlCommonOptions) options).set_generic(true);
			}
			
			try {
				fileAsString = QDoxUtil.getTypeErasureForTypeDeclsInFile(
						file, java5OrLater);
			} catch (FileNotFoundException e) {
				reportTrouble(e);
				return null;
			} catch (IOException e) {
				reportTrouble(e);
				return null;
			} catch(com.thoughtworks.qdox.parser.ParseException e){
				try {
					throw new PositionedError(
							TokenReference.build(file, e.getLine(),
									e.getColumn()),
							CompilerMessages.SYNTAX_ERROR,
							"please use the standard javac compiler for a detailed syntax error information [AspectJML].");
				} catch (PositionedError e1) {
					reportTrouble(e1);
				}
				return null;
			} catch (PositionedError e) {
				reportTrouble(e);
			} catch(Exception e) {
				try {
					reportTrouble(new Exception(file.getCanonicalPath()+" [error] internal error, please for a detailed error information, see the stack trace below [AspectJML]."));
					e.printStackTrace();
				} catch (IOException e1) {
					reportTrouble(e);
					return null;
				}
				return null;
			}
        	
        	buffer = new BufferedReader(new StringReader(fileAsString));

            JmlLexer jmlLexer;
            JavadocJmlLexer docLexer;
            JmlMLLexer jmlMLLexer;
            JmlSLLexer jmlSLLexer;
            JmlJDLexer jmlJDLexer;
            JmlParser parser = null; 
            JCompilationUnitType unit;

            // Used to switch lexers.  Aliases are created within the
            // lexer instances.
            TokenStreamSelector lexingController;
            ParsingController parsingController;

            Long duration = null;
            long lastTime = System.currentTimeMillis();

            parsingController = new ParsingController( buffer, file );
            lexingController = new TokenStreamSelector();
            final boolean allowJavaAssert = options.source().equals("1.4");
            final boolean allowResend = options.multijava();
	    setAllowUniverses( options.universesx() ); // WMD
	    
            jmlLexer = new JmlLexer( parsingController, lexingController,
                                     allowJavaAssert, allowResend,
				     allowUniverseKeywords, 
                                     Main.this );
                
            docLexer = new JavadocJmlLexer( parsingController );
            jmlMLLexer = new JmlMLLexer( parsingController, lexingController,
                                         allowJavaAssert, allowResend,
					 allowUniverseKeywords,
                                         Main.this );
            jmlJDLexer = new JmlJDLexer( parsingController, lexingController,
                                         allowJavaAssert, allowResend,
					 allowUniverseKeywords,
                                         Main.this );
            jmlSLLexer = new JmlSLLexer( parsingController, lexingController,
                                         allowJavaAssert, allowResend,
					 allowUniverseKeywords,
                                         Main.this );

            try {
                lexingController.addInputStream( jmlLexer, "jmlTop" );
                lexingController.addInputStream( jmlMLLexer, "jmlML" );
                lexingController.addInputStream( jmlJDLexer, "jmlJD" );
                lexingController.addInputStream( jmlSLLexer, "jmlSL" );
                lexingController.select( "jmlTop" );
                parsingController.addInputStream( lexingController, "jml" );
                parsingController.addInputStream( docLexer, "javadoc" );
                parsingController.selectInitial( "jml" );

                parser = 
                    new JmlParser( Main.this, 
                                   parsingController.initialOutputStream(),
                                   parsingController,
                                   options.generic(),
                                   options.multijava(), 
                                   options.relaxed(), 
				   allowUniverseKeywords, // WMD
				   isRefinedCUnit );

                unit = parser.jCompilationUnit();
                unit.cachePassParameters( Main.this, destination );
            } catch( ParsingController.ConfigurationException e ) {
		reportTrouble(new FormattedException(
                	MjcMessages.PARSER_INITIALIZATION_PROBLEM,
                        file.getName(), e.getMessage() ));
                unit = null;
            } catch( antlr.ANTLRException e ) {
            	reportTrouble( parser.beautifyParserError(e) );
            	unit = null;
            } catch(CompilationAbortedException e) {
                // The error will have already been noted
                // An example that gets here is to run jmldoc on a file such as TestRefines.java
                // but have a file like TestRefines.refines-java with an error like two refine clauses.
                unit = null;
            } catch( Exception e ) {
		reportTrouble(e);
                unit = null;
            } finally {
                duration = new Long( System.currentTimeMillis() - lastTime );
                try {
                    buffer.close();
                } catch( IOException e ) {
                    reportTrouble( e );
                }
            }

            if( verboseMode() ) {
                inform( CompilerMessages.FILE_PARSED, file.getPath(), 
                        duration );
            }

            // Some operations need to retrieve the Compilation Unit
            // AST, e.g., refinement and runtime assertion checking.
            JmlTypeLoader.getJmlSingleton().putCUnitAST(file, unit);

            return unit;
        }
    }

    /**
     * This class typechecks the source code.  The class is
     * constructed on an AST forest.  */
    public class JmlTypecheckTask extends TypecheckTask {
        /**
         * Constructs a task for checking the initializers in the given
         * forest.  Stores an alias to trees.  */
        public JmlTypecheckTask( CompilerPassEnterable[] trees, 
                                 Object sequenceID ) 
        {
            super(trees, sequenceID);
        }

        /**
         * Check that body of a given compilation unit is correct.
         *
         * @param       tree          the compilation unit
         */
        protected void processTree( CompilerPassEnterable tree ) {
            long lastTime = System.currentTimeMillis();
            if (!((JmlCommonOptions)options).Quiet()) {
                TokenReference where = tree.getTokenReference();
                String treeInfo = where.file().toString();
                if (tree instanceof JmlTypeDeclaration) {
                    treeInfo += " -- " + ((JmlTypeDeclaration)tree).ident();
                }
                inform(JmlMessages.TYPECHECKING, 
                       makeRelative(treeInfo,
                                    System.getProperty("user.dir"),
                                    File.separator) );
            }
            try {
                tree.typecheck();
            } catch( PositionedError e ) {
                reportTrouble( e );
            }
            if( verboseMode() ) {
                inform( CompilerMessages.BODY_CHECKED, 
                        tree.getTokenReference().file(),
                        new Long(System.currentTimeMillis() - lastTime) );
            }
        }

    }

     /**
      * A task for checking assignable clauses; this task has to 
      * be done after type checking of assignable clauses of 
      * the super types so the fields can be combined with those of 
      * the subtype (the subtype is the one whose code is being 
      * checked against the assignable clauses but the inherited 
      * assignable clauses need to be type checked first).
      * It is a subclass of TypecheckTask to avoid having to override 
      * any more of the conditions in the <code>createTaskAfter</code> 
      * method of Main.
      * The class is constructed on an AST forest.  
      */
     public class JmlCheckAssignableTask extends TypecheckTask {

         /**
          * Constructs a task for checking the assignable clauses 
          * of types in the given compilation units (trees). 
          * Removes all but the most refined compilation units
          * from the array of trees.  */
         public JmlCheckAssignableTask( CompilerPassEnterable[] trees,
                                        Object sequenceID ) {
             super( PRI_TYPECHECK+10, sequenceID, trees,
                    JmlMessages.ASSIGNABLE_CHECKING );

             // filter out all but most refined entries, i.e., those 
             // trees with the combined specifications for 
             // the types.
             ArrayList cunits = new ArrayList(trees.length);
             for (int i = 0; i < trees.length; i++) {
                 if ( trees[i] instanceof JmlCompilationUnit ) {
                     JmlCompilationUnit cunit 
                         = (JmlCompilationUnit) this.trees[i];

                     // add if not refined by another cunit?
                     if (! cunit.isRefined()) {
                         cunits.add(this.trees[i]);
                     }
                 }
             }
             this.trees = (CompilerPassEnterable[]) 
                 cunits.toArray(new CompilerPassEnterable[cunits.size()]);
         }

         /** Processes the given tree, <code>tree</code>. I.e.,
          * checks the assignable clauses in each AST representing 
          * the source file, i.e., compilation unit. */
         protected void processTree(CompilerPassEnterable tree) {
            long lastTime = System.currentTimeMillis();

             //@ assume tree != null && tree instanceof JmlCompilationUnit;

             JmlCompilationUnit cunit = (JmlCompilationUnit) tree;
            try {
                cunit.checkAssignableClauses();
            } catch( PositionedError e ) {
                reportTrouble( e );
            }
            if( verboseMode() ) {
                inform( passCompletedMessage, 
                        tree.getTokenReference().file(),
                        new Long(System.currentTimeMillis() - lastTime) );
            }
         }
     }

    //-------------------------------------------------------------------------
    //!FIXME! Change uses of this to the new Utils.relativepathTo method, after
    // making sure that they do the same thing.
    /** This function should return a path for the first argument that is
     * relative to the second argument (which may be a directory or a
     * file); if the paths are the same, an empty string is returned.
     */
    //@ requires path != null && referenceDir != null && separator != null;
    //@ ensures \result != null;
    public static String makeRelative(String path, String referenceDir,
                                      String separator)
    {

        File f = new File(path);
        ArrayList pathv = new ArrayList();
        ArrayList refv = new ArrayList();
        try {
            File ff = f.getAbsoluteFile().getCanonicalFile();
            while (ff != null) { pathv.add(0,ff.getName()); ff = ff.getParentFile(); }
            f = new File(referenceDir);
            if (! f.isDirectory()) f = f.getParentFile();
            ff = f.getAbsoluteFile().getCanonicalFile();
            while (ff != null) { refv.add(0,ff.getName()); ff = ff.getParentFile(); }
        } catch (Exception e) {
            return path;
        }
        int i = 0;
        int n = pathv.size();
        if (n > refv.size()) n = refv.size();
        while (i<n && pathv.get(i).equals(refv.get(i))) ++i;

        if (i == 0) return path;
        if (i == refv.size() && i == pathv.size()) return "";
                
        int up = refv.size() - i;
        String s = "";
        while (--up >= 0) s = s + ".." + separator;
        while (i < pathv.size()) s = s + pathv.get(i++) + separator;
        s = s.substring(0,s.length()-separator.length()); // trims off the last separator 
        //System.out.println("MAKEREL: " + path + " " + referenceDir + " " + s);
        return s;
    }

    public static boolean hasOptionXobspure() {
//        return "obspure".equals(jmlOptions.experiment());
    	return false;
    }

    /** 
     * Returns true iff the command-line option <code>-Xsym</code> or
     * <code>-Xsymr</code> is specified. This option lets the compiler
     * to parse external symbol table files instead of the source
     * files.
     */
    public static boolean hasOptionXsymr() {
//        return "sym".equals(jmlOptions.experiment())
//            || "symr".equals(jmlOptions.experiment());
    	return false;
    }

    /** 
     * Returns true iff the command-line option <code>-Xsym</code> or
     * <code>-Xsymw</code> is specified. This option lets the compiler
     * to generate external symbol table files as the compilation
     * result.
     */
    public static boolean hasOptionXsymw() {
//        return "sym".equals(jmlOptions.experiment()) 
//            || "symw".equals(jmlOptions.experiment());
    	return false;
    }
    
    public static boolean hasUnsafeOpWarningOption(){
//    	return jmlOptions.UnsafeOpWarnings();
    	return false;
    }

    /**
     * Tracks the set of task sequence IDs for tasks spawned to
     * process files refined by files on the main task sequence.
     * Tasks with sequence IDs in this set should not be prematurely
     * aborted but should be allowed to pass through all same compiler
     * passes as main sequence tasks.  */
    protected HashSet refinedFileSequenceSet = new HashSet();

    /**
     * The set of files specified on the command line to be processed 
     * during the current session.
     */
    private HashSet commandLineFiles = new HashSet();

    /** Command-line options.
     *
     * <pre><jml>
     * invariant jmlOptions == options;
     * </jml></pre>
     */
    public static JmlCommonOptions jmlOptions;
}
