// Generated from JmlCommonOptions.opt
package org.jmlspecs.checker;

import gnu.getopt.Getopt;
import gnu.getopt.LongOpt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedHashSet;

/** This class is automatically generated from JmlCommonOptions.opt
 *  and contains member fields corresponding to command-line options.
 */
public class JmlCommonOptions extends org.jmlspecs.checker.JmlVersionOptions {

  public JmlCommonOptions(String name) {
    super(name);
  }

  public JmlCommonOptions() {
    this("JmlCommon");
  }
  private String filter = "org.jmlspecs.checker.JMLDefaultWarningFilter";
  public /*@ pure @*/ String filter() { return filter; }
  public String set_filter(String filter) { 
    return this.filter = filter;
  }

  private boolean Quiet = false;
  public /*@ pure @*/ boolean Quiet() { return Quiet; }
  public boolean set_Quiet(boolean Quiet) { 
    return this.Quiet = Quiet;
  }

  private boolean purity = true;
  public /*@ pure @*/ boolean purity() { return purity; }
  public boolean set_purity(boolean purity) { 
    return this.purity = purity;
  }

  private boolean Assignable = true;
  public /*@ pure @*/ boolean Assignable() { return Assignable; }
  public boolean set_Assignable(boolean Assignable) { 
    return this.Assignable = Assignable;
  }

  private boolean assignable = true;
  public /*@ pure @*/ boolean assignable() { return assignable; }
  public boolean set_assignable(boolean assignable) { 
    return this.assignable = assignable;
  }

//  private String experiment = null;
//  public /*@ pure @*/ String experiment() { return experiment; }
//  public String set_experiment(String experiment) { 
//    return this.experiment = experiment;
//  }

  private boolean UnsafeOpWarnings = false;
  public /*@ pure @*/ boolean UnsafeOpWarnings() { return UnsafeOpWarnings; }
  public boolean set_UnsafeOpWarnings(boolean UnsafeOpWarnings) { 
    return this.UnsafeOpWarnings = UnsafeOpWarnings;
  }

//  private boolean multijava = false;
//  public /*@ pure @*/ boolean multijava() { return multijava; }
//  public boolean set_multijava(boolean multijava) { 
//    return this.multijava = multijava;
//  }
  
  private boolean noRepresentsError = false;
  public /*@ pure @*/ boolean noRepresentsAsError() { return noRepresentsError; }
  public boolean set_norepresentserror(boolean noRepresentsError) { 
    return this.noRepresentsError = noRepresentsError;
  }

  private String universesx = "no";
  public /*@ pure @*/ String universesx() { return universesx; }
  public String set_universesx(String universesx) { 
    return this.universesx = universesx;
  }

  private String excludefiles = "_JML_Test[.$]";
  public /*@ pure @*/ String excludefiles() { return excludefiles; }
  public String set_excludefiles(String excludefiles) { 
    return this.excludefiles = excludefiles;
  }

  private boolean defaultNonNull = true;
  public /*@ pure @*/ boolean defaultNonNull() { return defaultNonNull; }
  public boolean set_defaultNonNull(boolean defaultNonNull) { 
    return this.defaultNonNull = defaultNonNull;
  }

  private boolean nonnull = false;
  public /*@ pure @*/ boolean nonnull() { return nonnull; }
  public boolean set_nonnull(boolean nonnull) { 
    return this.nonnull = nonnull;
  }

  private String admissibility = "none";
  public /*@ pure @*/ String admissibility() { return admissibility; }
  public String set_admissibility(String admissibility) { 
    return this.admissibility = admissibility;
  }


  public boolean processOption(int code, Getopt g) {
    switch (code) {
    case 'f':
      filter = getString(g, ""); break;
    case 'Q':
      Quiet = !false; break;
    case 'p':
      purity = !true; break;
    case 'A':
      Assignable = !true; break;
    case 'a':
      assignable = !true; break;
//    case 'X':
//      experiment = getString(g, ""); break;
    case 'u':
      UnsafeOpWarnings = !false; break;
    case 'M':
    	noRepresentsError = !false;  break;
//    case 'M':
//      multijava = true;  break;
//    case 1001:
//      multijava = false;  break;
    case 'E':
      universesx = getString(g, ""); break;
    case 'e':
      universesx = Main.UNIVERSE_FULL;  break;
    case 1003:
      excludefiles = getString(g, ""); break;
    case 'n':
      defaultNonNull = !true; break;
    case 'N':
      nonnull = !false; break;
    case 1005:
      admissibility = getString(g, ""); break;
    default:
      return super.processOption(code, g);
    }
    return true;
  }

  public boolean setOption(String name, Object newValue) {
    if (name.equals("filter")) {
      set_filter(getString((String)newValue));
    } else if (name.equals("Quiet")) {
      set_Quiet(((Boolean)newValue).booleanValue());
    } else if (name.equals("purity")) {
      set_purity(((Boolean)newValue).booleanValue());
    } else if (name.equals("Assignable")) {
      set_Assignable(((Boolean)newValue).booleanValue());
    } else if (name.equals("assignable")) {
      set_assignable(((Boolean)newValue).booleanValue());
    } 
//    else if (name.equals("experiment")) {
//      set_experiment(getString((String)newValue));
//    } 
    else if (name.equals("UnsafeOpWarnings")) {
      set_UnsafeOpWarnings(((Boolean)newValue).booleanValue());
    } 
//    else if (name.equals("multijava")) {
//      set_multijava(((Boolean)newValue).booleanValue());
//    } 
    else if (name.equals("noRepresentsError")) {
    	set_norepresentserror(((Boolean)newValue).booleanValue());
    } 
    else if (name.equals("universesx")) {
      set_universesx(getString((String)newValue));
    } else if (name.equals("excludefiles")) {
      set_excludefiles(getString((String)newValue));
    } else if (name.equals("defaultNonNull")) {
      set_defaultNonNull(((Boolean)newValue).booleanValue());
    } else if (name.equals("nonnull")) {
      set_nonnull(((Boolean)newValue).booleanValue());
    } else if (name.equals("admissibility")) {
      set_admissibility(getString((String)newValue));
    } else {
      return super.setOption(name, newValue);
    }
    return true;
  }

  public HashMap getOptions() {
	    HashMap result = super.getOptions();
//	    result.put("filter", "  --filter, -f <qualified-name>:        Warning filter [org.jmlspecs.checker.JMLDefaultWarningFilter]");
	    result.put("Quiet", "  --Quiet, -Q:                          Shuts off all typechecking informational messages [false]");
	    result.put("purity", "  --purity, -p:                         Check for purity in JML specification expressions [true]");
//	    result.put("Assignable", "  --Assignable, -A:                     Check that a method with an assignable clause does not call methods that do not have an assignable clause [true]");
	    result.put("assignable", "  --assignable, -a:                     Check that each non-pure heavyweight method specification case has an assignable clause [true]");
//	    result.put("experiment", "  --experiment, -X <exp-feature>:       Specify experimental features such as symbol files (sym, symr, symw)");
//	    result.put("UnsafeOpWarnings", "  --UnsafeOpWarnings, -u:               Produces warnings if an unsafe arithmetic operators is used in an assertion for which the math mode has not been explicitly set. [false]");
//	    result.put("multijava", "  --multijava, -M:                      Accept MultiJava source code [false]");
	    result.put("noRepresentsError", "  --noRepresentsError, -M:              Consider the absence of represents clauses as Error [false]");
//	    result.put("nomultijava", "  --nomultijava:                        Do not accept Multijava source code");
//	    result.put("universesx", "  --universesx, -E <>:                  Universe type system: no, parse, check, full [no]");
//	    result.put("universes", "  --universes, -e:                      Enable Universe type modifiers and type checking");
	    result.put("excludefiles", "  --excludefiles <pattern>:             Pattern (regex) of file names to exclude from processing [_JML_Test[.$]]");
	    result.put("defaultNonNull", "  --defaultNonNull, -n:                 Make reference paramenters, fields and method return types non_null by default [true]");
//	    result.put("nonnull", "  --nonnull, -N:                        statistics of non_null application [false]");
//	    result.put("admissibility", "  --admissibility <>:                   Check admissibility of invariants and represents clauses: none, classical, ownership [none]");
	    
	    return result;
	  }


  public LinkedHashSet getLongname() {
    LinkedHashSet longname = super.getLongname();
    longname.add("filter");
    longname.add("Quiet");
    longname.add("purity");
    longname.add("Assignable");
    longname.add("assignable");
//    longname.add("experiment");
    longname.add("UnsafeOpWarnings");
//    longname.add("multijava");
    longname.add("noRepresentsError");
    longname.add("nomultijava");
    longname.add("universesx");
    longname.add("universes");
    longname.add("excludefiles");
    longname.add("defaultNonNull");
    longname.add("nonnull");
    longname.add("admissibility");

    return longname;
  }

  public Hashtable getType() {
    Hashtable type = super.getType();
    type.put("filter", "String");
    type.put("Quiet", "boolean");
    type.put("purity", "boolean");
    type.put("Assignable", "boolean");
    type.put("assignable", "boolean");
//    type.put("experiment", "String");
    type.put("UnsafeOpWarnings", "boolean");
//    type.put("multijava", "boolean");
    type.put("noRepresentsError", "boolean");
    type.put("nomultijava", "");
    type.put("universesx", "String");
    type.put("universes", "");
    type.put("excludefiles", "String");
    type.put("defaultNonNull", "boolean");
    type.put("nonnull", "boolean");
    type.put("admissibility", "String");

    return type;
  }


  public Hashtable getDefaultValue() {
    Hashtable defaultValue = super.getDefaultValue();
    defaultValue.put("filter", "org.jmlspecs.checker.JMLDefaultWarningFilter");
    defaultValue.put("Quiet", Boolean.valueOf(false));
    defaultValue.put("purity", Boolean.valueOf(true));
    defaultValue.put("Assignable", Boolean.valueOf(true));
    defaultValue.put("assignable", Boolean.valueOf(true));
//    defaultValue.put("experiment", "");
    defaultValue.put("UnsafeOpWarnings", Boolean.valueOf(false));
//    defaultValue.put("multijava", Boolean.valueOf(false));
    defaultValue.put("noRepresentsError", Boolean.valueOf(false));
    defaultValue.put("nomultijava", "");
    defaultValue.put("universesx", "no");
    defaultValue.put("universes", "");
    defaultValue.put("excludefiles", "_JML_Test[.$]");
    defaultValue.put("defaultNonNull", Boolean.valueOf(true));
    defaultValue.put("nonnull", Boolean.valueOf(false));
    defaultValue.put("admissibility", "none");

    return defaultValue;
  }


  public Hashtable getCurrentValue() {
    Hashtable currentValue = super.getCurrentValue();
    currentValue.put("filter", getNonNullString(filter));
    currentValue.put("Quiet", Boolean.valueOf(Quiet));
    currentValue.put("purity", Boolean.valueOf(purity));
    currentValue.put("Assignable", Boolean.valueOf(Assignable));
    currentValue.put("assignable", Boolean.valueOf(assignable));
//    currentValue.put("experiment", getNonNullString(experiment));
    currentValue.put("UnsafeOpWarnings", Boolean.valueOf(UnsafeOpWarnings));
//    currentValue.put("multijava", Boolean.valueOf(multijava));
    currentValue.put("noRepresentsError", Boolean.valueOf(noRepresentsError));
    currentValue.put("nomultijava", "");
    currentValue.put("universesx", getNonNullString(universesx));
    currentValue.put("universes", "");
    currentValue.put("excludefiles", getNonNullString(excludefiles));
    currentValue.put("defaultNonNull", Boolean.valueOf(defaultNonNull));
    currentValue.put("nonnull", Boolean.valueOf(nonnull));
    currentValue.put("admissibility", getNonNullString(admissibility));

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
    helpString.put("filter", getOptions().get("filter"));
    helpString.put("Quiet", getOptions().get("Quiet"));
    helpString.put("purity", getOptions().get("purity"));
    helpString.put("Assignable", getOptions().get("Assignable"));
    helpString.put("assignable", getOptions().get("assignable"));
//    helpString.put("experiment", getOptions().get("experiment"));
    helpString.put("UnsafeOpWarnings", getOptions().get("UnsafeOpWarnings"));
//    helpString.put("multijava", getOptions().get("multijava"));
    helpString.put("noRepresentsError", getOptions().get("noRepresentsError"));
    helpString.put("nomultijava", getOptions().get("nomultijava"));
    helpString.put("universesx", getOptions().get("universesx"));
    helpString.put("universes", getOptions().get("universes"));
    helpString.put("excludefiles", getOptions().get("excludefiles"));
    helpString.put("defaultNonNull", getOptions().get("defaultNonNull"));
    helpString.put("nonnull", getOptions().get("nonnull"));
    helpString.put("admissibility", getOptions().get("admissibility"));

    return helpString;
  }


  public Hashtable getGuiType() {
    Hashtable guiType = super.getGuiType();
    guiType.put("filter", "advanced");
    guiType.put("Quiet", "normal");
    guiType.put("purity", "normal");
    guiType.put("Assignable", "normal");
    guiType.put("assignable", "normal");
//    guiType.put("experiment", "advanced");
    guiType.put("UnsafeOpWarnings", "normal");
//    guiType.put("multijava", "normal");
    guiType.put("noRepresentsError", "normal");
    guiType.put("nomultijava", "normal");
    guiType.put("universesx", "normal");
    guiType.put("universes", "normal");
    guiType.put("excludefiles", "advanced");
    guiType.put("defaultNonNull", "normal");
    guiType.put("nonnull", "normal");
    guiType.put("admissibility", "normal");

    return guiType;
  }


  public String getShortOptions() {
    return "f:QpAaX:uME:enN" + super.getShortOptions();
  }


  public void usage() {
    System.err.println("");
    printVersion();  }


  public void help() {
    System.err.println("");
    printOptions();
    System.err.println();
    System.err.println("This program includes some code from the Kopi project: http://www.dms.at/kopi");
    System.err.println("Some code for this program was generated with ANTLR: http://www.antlr.org");
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
    new LongOpt("filter", LongOpt.REQUIRED_ARGUMENT, null, 'f'),
    new LongOpt("Quiet", LongOpt.NO_ARGUMENT, null, 'Q'),
    new LongOpt("purity", LongOpt.NO_ARGUMENT, null, 'p'),
    new LongOpt("Assignable", LongOpt.NO_ARGUMENT, null, 'A'),
    new LongOpt("assignable", LongOpt.NO_ARGUMENT, null, 'a'),
//    new LongOpt("experiment", LongOpt.REQUIRED_ARGUMENT, null, 'X'),
    new LongOpt("UnsafeOpWarnings", LongOpt.NO_ARGUMENT, null, 'u'),
//    new LongOpt("multijava", LongOpt.NO_ARGUMENT, null, 'M'),
    new LongOpt("noRepresentsError", LongOpt.NO_ARGUMENT, null, 'M'),
    new LongOpt("nomultijava", LongOpt.NO_ARGUMENT, null, 1001),
    new LongOpt("universesx", LongOpt.REQUIRED_ARGUMENT, null, 'E'),
    new LongOpt("universes", LongOpt.NO_ARGUMENT, null, 'e'),
    new LongOpt("excludefiles", LongOpt.REQUIRED_ARGUMENT, null, 1003),
    new LongOpt("defaultNonNull", LongOpt.NO_ARGUMENT, null, 'n'),
    new LongOpt("nonnull", LongOpt.NO_ARGUMENT, null, 'N'),
    new LongOpt("admissibility", LongOpt.REQUIRED_ARGUMENT, null, 1005)
  };
}
