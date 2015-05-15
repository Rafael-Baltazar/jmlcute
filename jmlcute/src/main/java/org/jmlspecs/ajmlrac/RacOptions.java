// Generated from RacOptions.opt
package org.jmlspecs.ajmlrac;

import gnu.getopt.Getopt;
import gnu.getopt.LongOpt;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.HashMap;
import java.util.LinkedHashSet;

/** This class is automatically generated from RacOptions.opt
 *  and contains member fields corresponding to command-line options.
 */
public class RacOptions extends org.jmlspecs.checker.JmlCommonOptions {

  public RacOptions(String name) {
    super(name);
  }

  public RacOptions() {
    this("Rac");
  }
  private boolean print = false;
  public /*@ pure @*/ boolean print() { return print; }
  public boolean set_print(boolean print) { 
    return this.print = print;
  }

  private boolean nowrite = false;
  public /*@ pure @*/ boolean nowrite() { return nowrite; }
  public boolean set_nowrite(boolean nowrite) { 
    return this.nowrite = nowrite;
  }

   // now for aspectpath
//  private boolean noreflection = false;
//  public /*@ pure @*/ boolean noreflection() { return noreflection; }
//  public boolean set_noreflection(boolean noreflection) { 
//    return this.noreflection = noreflection;
//  }

  private boolean noredundancy = false;
  public /*@ pure @*/ boolean noredundancy() { return noredundancy; }
  public boolean set_noredundancy(boolean noredundancy) { 
    return this.noredundancy = noredundancy;
  }

  private boolean recursiveType = false;
  public /*@ pure @*/ boolean recursiveType() { return recursiveType; }
  public boolean set_recursiveType(boolean recursiveType) { 
    return this.recursiveType = recursiveType;
  }

  private String packageName = null;
  public /*@ pure @*/ String packageName() { return packageName; }
  public String set_packageName(String packageName) { 
    return this.packageName = packageName;
  }

  private boolean showWeaveInfo = false;
  public /*@ pure @*/ boolean showWeaveInfo() { return showWeaveInfo; }
  public boolean set_showWeaveInfo(boolean showWeaveInfo) { 
    return this.showWeaveInfo = showWeaveInfo;
  }

  // now for crossrefs for XCS mode on
//  private boolean neutralContext = false;
//  public /*@ pure @*/ boolean neutralContext() { return neutralContext; }
//  public boolean set_neutralContext(boolean neutralContext) { 
//    return this.neutralContext = neutralContext;
//  }
  
  private String crossrefs = null;
  public /*@ pure @*/ String crossrefs() { return crossrefs; }
  public String set_crossrefs(String crossrefs) { 
    return this.crossrefs = crossrefs;
  }

  private String filter = "org.jmlspecs.ajmlrac.JMLRacWarningFilter";
  public /*@ pure @*/ String filter() { return filter; }
  public String set_filter(String filter) { 
    return this.filter = filter;
  }

  // now for XCS
//  private boolean oldSemantics = false;
//  public /*@ pure @*/ boolean oldSemantics() { return oldSemantics; }
//  public boolean set_oldSemantics(boolean oldSemantics) { 
//    return this.oldSemantics = oldSemantics;
//  }

  private boolean mustBeExecutable = false;
  public /*@ pure @*/ boolean mustBeExecutable() { return mustBeExecutable; }
  public boolean set_mustBeExecutable(boolean mustBeExecutable) { 
    return this.mustBeExecutable = mustBeExecutable;
  }

  private String ajWeaver = "ajc";
  public /*@ pure @*/ String ajWeaver() { return ajWeaver; }
  public String set_ajWeaver(String ajWeaver) { 
    return this.ajWeaver = ajWeaver;
  }
  
  private boolean noExecutionSiteInstrumentation = false;
  public /*@ pure @*/ boolean noExecutionSiteInstrumentation() { return noExecutionSiteInstrumentation; }
  public boolean set_noExecutionSiteInstrumentation(boolean noExecutionSiteInstrumentation) { 
    return this.noExecutionSiteInstrumentation = noExecutionSiteInstrumentation;
  }

  private boolean callSiteInstrumentation = false;
  public /*@ pure @*/ boolean callSiteInstrumentation() { return callSiteInstrumentation; }
  public boolean set_callSiteInstrumentation(boolean callSiteInstrumentation) { 
    return this.callSiteInstrumentation = callSiteInstrumentation;
  }

  private boolean clientAwareChecking = false;
  public /*@ pure @*/ boolean clientAwareChecking() { return clientAwareChecking; }
  public boolean set_clientAwareChecking(boolean clientAwareChecking) { 
    return this.clientAwareChecking = clientAwareChecking;
  }
  
  private boolean multipleSpecCaseChecking = false;
  public /*@ pure @*/ boolean multipleSpecCaseChecking() { return multipleSpecCaseChecking; }
  public boolean set_multipleSpecCaseChecking(boolean multipleSpecCaseChecking) { 
    return this.multipleSpecCaseChecking = multipleSpecCaseChecking;
  }
  
  private boolean crosscuttingContractSpecifications = true;
  public /*@ pure @*/ boolean crosscuttingContractSpecifications() { return crosscuttingContractSpecifications; }
  public boolean set_crosscuttingContractSpecifications(boolean crosscuttingContractSpecifications) { 
    return this.crosscuttingContractSpecifications = crosscuttingContractSpecifications;
  }
  
  private boolean adviceChecking = true;
  public /*@ pure @*/ boolean adviceChecking() { return adviceChecking; }
  public boolean set_adviceChecking(boolean adviceChecking) { 
    return this.adviceChecking = adviceChecking;
  }

  private String inpath = null;
  public /*@ pure @*/ String inpath() { return inpath; }
  public String set_inpath(String inpath) { 
    return this.inpath = inpath;
  }
  
  private String outjar = null;
  public /*@ pure @*/ String outjar() { return outjar; }
  public String set_outjar(String outjar) { 
    return this.outjar = outjar;
  }
  
  private String aspectpath = null;
  public /*@ pure @*/ String aspectpath() { return aspectpath; }
  public String set_aspectpath(String aspectpath) { 
    return this.aspectpath = aspectpath;
  }
  
  public boolean processOption(int code, Getopt g) {
	  switch (code) {
	  case 'P':
		  print = !false; break;
	  case 'W':
		  nowrite = !false; break;
//	  case 'F':
//		  noreflection = !false; break;
	  case 'F':
	    	aspectpath = getString(g, "null"); break;  // ajmlc
	  case 'Y':
		  noredundancy = !false; break;
	  case 't':
		  recursiveType = !false; break;
	  case 'N':
		  packageName = getString(g, ""); break;
	  case 'u':
		  showWeaveInfo = !false; break;
	  case 'o':
		  crossrefs = getString(g, "null"); break;  // ajmlc
	  case 'f':
		  filter = getString(g, ""); break;
//	  case 'O':
//		  oldSemantics = !false; break;
	  case 'X':
		  crosscuttingContractSpecifications = !false; break; // ajmlc
	  case 'O':
		  adviceChecking = !false; break;	  // ajmlc
	  case 'V':
		  mustBeExecutable = !false; break;
	  // new options for ajmlc
	    case 'H':
	      ajWeaver = getString(g, ""); break;
	    case 'y':
	        noExecutionSiteInstrumentation = !false; break;
	    case 'b':
	      callSiteInstrumentation = !false; break;
	    case 'B':
	      clientAwareChecking = !false; break;
	    case 'l':
	      multipleSpecCaseChecking = !false; break;
	    case 'I':
	      inpath = getString(g, "null"); break;
	    case 'i':
	        outjar = getString(g, "null"); break;
	  default:
		  return super.processOption(code, g);
	  }
	  return true;
  }
  
  public boolean setOption(String name, Object newValue) {
	    if (name.equals("print")) {
	      set_print(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("nowrite")) {
	      set_nowrite(((Boolean)newValue).booleanValue());
	    } 
//	    else if (name.equals("noreflection")) {
//	      set_noreflection(((Boolean)newValue).booleanValue());
//	    } 
	    else if (name.equals("noredundancy")) {
	      set_noredundancy(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("recursiveType")) {
	      set_recursiveType(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("packageName")) {
	      set_packageName(getString((String)newValue));
	    } 
	    else if (name.equals("showWeaveInfo")) {
	      set_showWeaveInfo(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("crossrefs")) {
	      set_crossrefs(getString((String)newValue));
	    } 
	    else if (name.equals("filter")) {
	      set_filter(getString((String)newValue));
	    } 
//	    else if (name.equals("oldSemantics")) {
//	      set_oldSemantics(((Boolean)newValue).booleanValue());
//	    } 
	    else if (name.equals("mustBeExecutable")) {
	      set_mustBeExecutable(((Boolean)newValue).booleanValue());
	    } 
	    // new options for ajmlc
	    else if (name.equals("ajWeaver")) {
	      set_ajWeaver(getString((String)newValue));
	    } 
	    else if (name.equals("noExecutionSiteInstrumentation")) {
	        set_noExecutionSiteInstrumentation(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("callSiteInstrumentation")) {
	      set_callSiteInstrumentation(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("clientAwareChecking")) {
	      set_clientAwareChecking(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("multipleSpecCaseChecking")) {
	      set_multipleSpecCaseChecking(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("crosscuttingContractSpecifications")) {
	    	set_crosscuttingContractSpecifications(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("adviceChecking")) {
	    	set_adviceChecking(((Boolean)newValue).booleanValue());
	    } 
	    else if (name.equals("inpath")) {
	      set_inpath(getString((String)newValue));
	    } 
	    else if (name.equals("outjar")) {
	      set_outjar(getString((String)newValue));
	    } 
	    else if (name.equals("aspectpath")) {
	      set_aspectpath(getString((String)newValue));
	    }
	    else {
	      return super.setOption(name, newValue);
	    }
	    return true;
	  }

  public HashMap getOptions() {
    HashMap result = super.getOptions();
    result.put("print", "  --print, -P:                          Prints instrumented source code instead of bytecode [false]");
    result.put("nowrite", "  --nowrite, -W:                        Only typechecks files, doesn't generate code [false]");
//    result.put("noreflection", "  --noreflection, -F:                   Don't use reflection for specification inheritance [false]"); // in use
    result.put("noredundancy", "  --noredundancy, -Y:                   Don't check redundant specifications [false]");
//    result.put("recursiveType", "  --recursiveType, -t:                  Enable typechecking of recursively referenced types [false]");
//    result.put("packageName", "  --packageName, -N <pkg-name>:         Package name or prefix");
    result.put("showWeaveInfo", "  --showWeaveInfo, -u:                  Emit messages about JML specifications/contracts weaving [false]");
//    result.put("neutralContext", "  --neutralContext, -o:                 use neutral context instead of contextual interpretation [false]"); // in use
//    result.put("filter", "  --filter, -f <qualified-name>:        Warning filter [org.jmlspecs.ajmlrac.JMLRacWarningFilter]");
//    result.put("oldSemantics", "  --oldSemantics, -O:                   use old expression translation mecanism that emulates 2-valued logic [false]"); // in use
    result.put("crossrefs", "  --crossrefs, -o:               Generate a build .aj file into the specified output directory. Used for viewing crosscutting references by tools like the AJDT/AspectJ Browser");
    result.put("mustBeExecutable", "  --mustBeExecutable, -V:               consider non-executable clauses as false assertions [false]");
    result.put("ajWeaver", "  --ajWeaver, -H:                       AspectJ weaver for assertion instrumentation [ajc]");
    result.put("noExecutionSiteInstrumentation", "  --noExecutionSiteInstrumentation, -y: Disable execution site instrumentation and checking [false]");
    result.put("callSiteInstrumentation", "  --callSiteInstrumentation, -b:        Enable call site instrumentation and checking [false]");
    result.put("clientAwareChecking", "  --clientAwareChecking, -B:            Enable client-aware checking technique. This technique turns off execution site instrumentation [false]");
    result.put("multipleSpecCaseChecking", "  --multipleSpecCaseChecking, -l:       Enable multiple specification case checking [false]");
    result.put("crosscuttingContractSpecifications", "  --crosscuttingContractSpecifications, -X:   Enable crosscutting contracts declared in the form of specifications to be modularly checked at the advised/intercepted code. " +
    		"\n                                              Note that --crosscuttingContractSpecifications option uses some reflective capabilities of AspectJ API [true]");
    result.put("adviceChecking", "  --adviceChecking, -O:                 Enable @AspectJ advice contract checking [true]");
    result.put("inpath", "  --inpath, -I:                         Accept as source bytecode any .class files in the .jar files or directories on Path");
    result.put("outjar", "  --outjar, -i:                         Put woven output classes in zip file output.jar");
    result.put("aspectpath", "  --aspectpath, -F:                     Weave aspects in .class files from <list> dirs and jars/zip into sources (<list> uses classpath delimiter)");
    
    return result;
  }


  public LinkedHashSet getLongname() {
    LinkedHashSet longname = super.getLongname();
    longname.add("print");
    longname.add("nowrite");
//    longname.add("noreflection");
    longname.add("noredundancy");
    longname.add("recursiveType");
    longname.add("packageName");
    longname.add("showWeaveInfo");
    longname.add("crossrefs");
    longname.add("filter");
//    longname.add("oldSemantics");
    longname.add("mustBeExecutable");
    longname.add("ajWeaver");
    longname.add("noExecutionSiteInstrumentation");
    longname.add("callSiteInstrumentation");
    longname.add("clientAwareChecking");
    longname.add("multipleSpecCaseChecking");
    longname.add("crosscuttingContractSpecifications");
    longname.add("adviceChecking");
    longname.add("inpath");
    longname.add("outjar");
    longname.add("aspectpath");

    return longname;
  }

  public Hashtable getType() {
    Hashtable type = super.getType();
    type.put("print", "boolean");
    type.put("nowrite", "boolean");
//    type.put("noreflection", "boolean");
    type.put("noredundancy", "boolean");
    type.put("recursiveType", "boolean");
    type.put("packageName", "String");
    type.put("showWeaveInfo", "boolean");
    type.put("crossrefs", "String");
    type.put("filter", "String");
//    type.put("oldSemantics", "boolean");
    type.put("mustBeExecutable", "boolean");
    type.put("ajWeaver", "String");
    type.put("noExecutionSiteInstrumentation", "boolean");
    type.put("callSiteInstrumentation", "boolean");
    type.put("clientAwareChecking", "boolean");
    type.put("multipleSpecCaseChecking", "boolean");
    type.put("crosscuttingContractSpecifications", "boolean");
    type.put("adviceChecking", "boolean");
    type.put("inpath", "String");
    type.put("outjar", "String");
    type.put("aspectpath", "String");

    return type;
  }


  public Hashtable getDefaultValue() {
    Hashtable defaultValue = super.getDefaultValue();
    defaultValue.put("print", Boolean.valueOf(false));
    defaultValue.put("nowrite", Boolean.valueOf(false));
//    defaultValue.put("noreflection", Boolean.valueOf(false));
    defaultValue.put("noredundancy", Boolean.valueOf(false));
    defaultValue.put("recursiveType", Boolean.valueOf(false));
    defaultValue.put("packageName", "");
    defaultValue.put("showWeaveInfo", Boolean.valueOf(false));
    defaultValue.put("crossrefs", "");
    defaultValue.put("filter", "org.jmlspecs.jmlrac.JMLRacWarningFilter");
//    defaultValue.put("oldSemantics", Boolean.valueOf(false));
    defaultValue.put("mustBeExecutable", Boolean.valueOf(false));
    defaultValue.put("ajWeaver", "ajc");
    defaultValue.put("noExecutionSiteInstrumentation", Boolean.valueOf(false));
    defaultValue.put("callSiteInstrumentation", Boolean.valueOf(false));
    defaultValue.put("clientAwareChecking", Boolean.valueOf(false));
    defaultValue.put("multipleSpecCaseChecking", Boolean.valueOf(false));
    defaultValue.put("crosscuttingContractSpecifications", Boolean.valueOf(true));
    defaultValue.put("adviceChecking", Boolean.valueOf(true));
    defaultValue.put("inpath", "");
    defaultValue.put("outjar", "");
    defaultValue.put("aspectpath", "");
    return defaultValue;
  }


  public Hashtable getCurrentValue() {
    Hashtable currentValue = super.getCurrentValue();
    currentValue.put("print", Boolean.valueOf(print));
    currentValue.put("nowrite", Boolean.valueOf(nowrite));
//    currentValue.put("noreflection", Boolean.valueOf(noreflection));
    currentValue.put("noredundancy", Boolean.valueOf(noredundancy));
    currentValue.put("recursiveType", Boolean.valueOf(recursiveType));
    currentValue.put("packageName", getNonNullString(packageName));
    currentValue.put("showWeaveInfo", Boolean.valueOf(showWeaveInfo));
    currentValue.put("crossrefs", getNonNullString(crossrefs));
    currentValue.put("filter", getNonNullString(filter));
//    currentValue.put("oldSemantics", Boolean.valueOf(oldSemantics));
    currentValue.put("mustBeExecutable", Boolean.valueOf(mustBeExecutable));
    currentValue.put("ajWeaver", getNonNullString(ajWeaver));
    currentValue.put("noExecutionSiteInstrumentation", Boolean.valueOf(noExecutionSiteInstrumentation));
    currentValue.put("callSiteInstrumentation", Boolean.valueOf(callSiteInstrumentation));
    currentValue.put("clientAwareChecking", Boolean.valueOf(clientAwareChecking));
    currentValue.put("multipleSpecCaseChecking", Boolean.valueOf(multipleSpecCaseChecking));
    currentValue.put("crosscuttingContractSpecifications", Boolean.valueOf(crosscuttingContractSpecifications));
    currentValue.put("adviceChecking", Boolean.valueOf(adviceChecking));
    currentValue.put("inpath", getNonNullString(inpath));
    currentValue.put("outjar", getNonNullString(outjar));
    currentValue.put("aspectpath", getNonNullString(aspectpath));
    return currentValue;
  }

  public Hashtable getTableHeader() {
    Hashtable tableHeader = super.getTableHeader();
    return tableHeader;
  }

  public Hashtable getSelectionList() {
    Hashtable selectionHash = super.getSelectionList();
    ArrayList selectionChoices;
    return selectionHash;
  }

  public Hashtable getHelpString() {
    Hashtable helpString = super.getHelpString();
    helpString.put("print", getOptions().get("print"));
    helpString.put("nowrite", getOptions().get("nowrite"));
//    helpString.put("noreflection", getOptions().get("noreflection"));
    helpString.put("noredundancy", getOptions().get("noredundancy"));
    helpString.put("recursiveType", getOptions().get("recursiveType"));
    helpString.put("packageName", getOptions().get("packageName"));
    helpString.put("showWeaveInfo", getOptions().get("showWeaveInfo"));
    helpString.put("crossrefs", getOptions().get("crossrefs"));
    helpString.put("filter", getOptions().get("filter"));
//    helpString.put("oldSemantics", getOptions().get("oldSemantics"));
    helpString.put("mustBeExecutable", getOptions().get("mustBeExecutable"));
    helpString.put("ajWeaver", getOptions().get("ajWeaver"));
    helpString.put("noExecutionSiteInstrumentation", getOptions().get("noExecutionSiteInstrumentation"));
    helpString.put("callSiteInstrumentation", getOptions().get("callSiteInstrumentation"));
    helpString.put("clientAwareChecking", getOptions().get("clientAwareChecking"));
    helpString.put("multipleSpecCaseChecking", getOptions().get("multipleSpecCaseChecking"));
    helpString.put("crosscuttingContractSpecifications", getOptions().get("crosscuttingContractSpecifications"));
    helpString.put("adviceChecking", getOptions().get("adviceChecking"));
    helpString.put("inpath", getOptions().get("inpath"));
    helpString.put("outjar", getOptions().get("outjar"));
    helpString.put("aspectpath", getOptions().get("aspectpath"));
    return helpString;
  }


  public Hashtable getGuiType() {
    Hashtable guiType = super.getGuiType();
    guiType.put("print", "advanced");
    guiType.put("nowrite", "advanced");
//    guiType.put("noreflection", "normal");
    guiType.put("noredundancy", "normal");
    guiType.put("recursiveType", "advanced");
    guiType.put("packageName", "advanced");
    guiType.put("showWeaveInfo", "advanced");
    guiType.put("crossrefs", "advanced");
    guiType.put("filter", "advanced");
//    guiType.put("oldSemantics", "advanced");
    guiType.put("mustBeExecutable", "advanced");
    guiType.put("ajWeaver", "advanced");
    guiType.put("noExecutionSiteInstrumentation", "advanced");
    guiType.put("callSiteInstrumentation", "advanced");
    guiType.put("clientAwareChecking", "advanced");
    guiType.put("multipleSpecCaseChecking", "advanced");
    guiType.put("crosscuttingContractSpecifications", "advanced");
    guiType.put("adviceChecking", "advanced");
    guiType.put("inpath", "advanced");
    guiType.put("outjar", "outjar");
    guiType.put("aspectpath", "aspectpath");
    return guiType;
  }

  public String getShortOptions() {
    return "PWFYtN:uof:XOV HybBlxIi" + super.getShortOptions();
  }


  public void usage() {
    System.err.println("usage: org.jmlspecs.ajmlrac.Main [option]* [--help] <aspectjml-files>");
    printVersion();  }


  public void help() {
    System.err.println("usage: org.jmlspecs.ajmlrac.Main [option]* [--help] <aspectjml-files>");
    printOptions();
    System.err.println();
    System.out.println("This program is part of the AspectJML project: http://www.cin.ufpe.br/~hemr/JMLAOP/aspectjml\nThe code extends code from the JML project: http://www.jmlspecs.org");
    System.out.println("This program includes the QDox parser from the QDox project: http://qdox.codehaus.org/");
    System.out.println("This program includes some code from the Kopi project: http://www.dms.at/kopi");
    System.out.println("Some code for this program was generated with ANTLR: http://www.antlr.org");
    printVersion();
  }

  public LongOpt[] getLongOptions() {
    LongOpt[]      parent = super.getLongOptions();
    LongOpt[]      total = new LongOpt[parent.length + LONGOPTS.length];
    
    System.arraycopy(parent, 0, total, 0, parent.length);
    System.arraycopy(LONGOPTS, 0, total, parent.length, LONGOPTS.length);
    
    return total;
  }

  private static final LongOpt[] LONGOPTS = {
	  new LongOpt("print", LongOpt.NO_ARGUMENT, null, 'P'),
	  new LongOpt("nowrite", LongOpt.NO_ARGUMENT, null, 'W'),
	  //	    new LongOpt("noreflection", LongOpt.NO_ARGUMENT, null, 'F'),
	  new LongOpt("noredundancy", LongOpt.NO_ARGUMENT, null, 'Y'),
	  new LongOpt("recursiveType", LongOpt.NO_ARGUMENT, null, 't'),
	  new LongOpt("packageName", LongOpt.REQUIRED_ARGUMENT, null, 'N'),
	  new LongOpt("showWeaveInfo", LongOpt.NO_ARGUMENT, null, 'u'),
	  new LongOpt("crossrefs", LongOpt.REQUIRED_ARGUMENT, null, 'o'),
	  new LongOpt("filter", LongOpt.REQUIRED_ARGUMENT, null, 'f'),
	  //	    new LongOpt("oldSemantics", LongOpt.NO_ARGUMENT, null, 'O'),
	  new LongOpt("mustBeExecutable", LongOpt.NO_ARGUMENT, null, 'V'),
	  new LongOpt("ajWeaver", LongOpt.REQUIRED_ARGUMENT, null, 'H'),
	  new LongOpt("noExecutionSiteInstrumentation", LongOpt.NO_ARGUMENT, null, 'y'),
	  new LongOpt("callSiteInstrumentation", LongOpt.NO_ARGUMENT, null, 'b'),
	  new LongOpt("clientAwareChecking", LongOpt.NO_ARGUMENT, null, 'B'),
	  new LongOpt("multipleSpecCaseChecking", LongOpt.NO_ARGUMENT, null, 'l'),
	  new LongOpt("crosscuttingContractSpecifications", LongOpt.NO_ARGUMENT, null, 'X'),
	  new LongOpt("adviceChecking", LongOpt.NO_ARGUMENT, null, 'O'),
	  new LongOpt("inpath", LongOpt.REQUIRED_ARGUMENT, null, 'I'),
	  new LongOpt("outjar", LongOpt.REQUIRED_ARGUMENT, null, 'i'),
	  new LongOpt("aspectpath", LongOpt.REQUIRED_ARGUMENT, null, 'F'),
  };
}
