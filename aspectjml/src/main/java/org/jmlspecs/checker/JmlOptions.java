// Generated from JmlOptions.opt
package org.jmlspecs.checker;

import gnu.getopt.Getopt;
import gnu.getopt.LongOpt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedHashSet;

/** This class is automatically generated from JmlOptions.opt
 *  and contains member fields corresponding to command-line options.
 */
public class JmlOptions extends org.jmlspecs.checker.JmlCommonOptions {

  public JmlOptions(String name) {
    super(name);
  }

  public JmlOptions() {
    this("Jml");
  }

  public boolean processOption(int code, Getopt g) {
    switch (code) {
    default:
      return super.processOption(code, g);
    }
  }

  public boolean setOption(String name, Object newValue) {
    {
      return super.setOption(name, newValue);
    }
  }

  public HashMap getOptions() {
    HashMap result = super.getOptions();
    
    return result;
  }


  public LinkedHashSet getLongname() {
    LinkedHashSet longname = super.getLongname();

    return longname;
  }

  public Hashtable getType() {
    Hashtable type = super.getType();

    return type;
  }


  public Hashtable getDefaultValue() {
    Hashtable defaultValue = super.getDefaultValue();

    return defaultValue;
  }


  public Hashtable getCurrentValue() {
    Hashtable currentValue = super.getCurrentValue();

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

    return helpString;
  }


  public Hashtable getGuiType() {
    Hashtable guiType = super.getGuiType();

    return guiType;
  }


  public String getShortOptions() {
    return "" + super.getShortOptions();
  }


  public void usage() {
    System.err.println("usage: org.jmlspecs.checker.Main [option]* [--help] <jml-files>");
    printVersion();  }


  public void help() {
    System.err.println("usage: org.jmlspecs.checker.Main [option]* [--help] <jml-files>");
    printOptions();
    System.err.println();
    System.err.println("This program is part of the JML project: http://www.jmlspecs.org\nThe code extends code from the MultiJava project: http://www.multijava.org");
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

  };
}
