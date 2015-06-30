/*
 * Copyright (C) 2001 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: PreValueVars.java,v 1.7 2003/01/14 11:41:26 davidcok Exp $
 */

package org.jmlspecs.ajmlrac;

import java.util.Iterator;
import java.util.ArrayList;

/**
 * A container class to store information about private fields that
 * are used to pass pre-state values, typically computed by
 * precondition check methods, to postcondition check
 * methods. Examples of such values are preconditions themselves, old
 * variables, old expressions appearing both in postconditions and
 * history constraints.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.7 $
 */
class PreValueVars implements RacConstants {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /** Constructs a new instance. */
    PreValueVars() {
    }

    /** Returns a new JMLValue variable declaration. */
    static Entry createJmlValueVar(boolean isStatic, String name) {
        return new Entry(isStatic, TN_JMLVALUE, name, NULL);
    }

    /** Returns a new boolean variable declaration. */
    static Entry createBooleanVar(boolean isStatic, String name) {
        return new Entry(isStatic, BOOLEAN, name, FALSE);
    }

    /** Returns a new variable declaration. */
    static Entry createVar(boolean isStatic, String type,
                                  String name, String value) {
        return new Entry(isStatic, type, name, value);
    }

    // ----------------------------------------------------------------------
    // QUERY METHODS
    // ----------------------------------------------------------------------
    
    /** Returns true if there is no variable declaration. */
    boolean isEmpty() {
        return variables.isEmpty();
    }
    
    // ----------------------------------------------------------------------
    // ADDING
    // ----------------------------------------------------------------------
    
    /** Adds the given field. */
    void add(boolean isStatic, String type, String name, String value) {
        variables.add(new Entry(isStatic, type, name, value));
    }

    /** Adds the given field of type JMLValue with the default value. */
    void addJmlValue(boolean isStatic, String name) {
        add(isStatic, TN_JMLVALUE, name, NULL);
    }

    /** Adds the given field of type boolean with the default value. */
    void addBoolean(boolean isStatic, String name) {
        add(isStatic, BOOLEAN, name, FALSE);
    }

    /** Adds all the given field declarations. */
    void addAll(/*@ non_null @*/ Entry[] decls) {
        for (int i = 0; i < decls.length; i++) {
            variables.add(decls[i]);
        }
    }

    /** Adds the given field declaration. */
    void add(/*@ non_null @*/ Entry decl) {
        variables.add(decl);
    }

    // ----------------------------------------------------------------------
    // PRINTING SOURCE CODE
    // ----------------------------------------------------------------------
    
    /** Returns a piece of code that, if executed, saves the values of
     * private fields contained in this object into local temporary
     * variables. If there is no field contained, null is
     * returned. Otherwise, the returned code has the following
     * structure.
     *
     * <pre>
     *  T1 cv1 = v1;
     *  ...
     *  Tn cvn = vn;
     * </pre>
     *
     * @see #restoreCode()
     */
    RacNode saveCode() {
        if (variables.isEmpty()) {
            return null;
        }
        StringBuffer code = new StringBuffer();
        code.append("// save pre-state vaules for possible recursion\n");
        for (Iterator i = variables.iterator(); i.hasNext(); ) {
            Entry e = (Entry) i.next();
            code.append(e.type + " " + PREFIX + e.name + " = " +e.name+ ";\n");
        }
        return RacParser.parseStatement(code.toString()).incrIndent();
    }

    /** Return a piece of code that, if executed, restored the values
     * of private fields contained in this object from their
     * corresponding local temporary variables. If there is no
     * field contained, null is returned. Otherwise, the returned code
     * has the following structure.
     *
     * <pre>
     *  v1 = cv1;
     *  ...
     *  cn = cvn;
     * </pre>
     *
     * @see #saveCode()
     */
    RacNode restoreCode() {
        if (variables.isEmpty()) {
            return null;
        }
        StringBuffer code = new StringBuffer();
        code.append("// restore pre-state vaules from possible recursion\n");
        for (Iterator i = variables.iterator(); i.hasNext(); ) {
            Entry e = (Entry) i.next();
            code.append(e.name + " = " + PREFIX + e.name + ";\n");
        }
        RacNode node = RacParser.parseStatement(code.toString());
        return node.incrIndent().incrIndent();
    }

    RacNode saveCode(/*@ non_null @*/ String var) {
        if (variables.isEmpty()) {
            return null;
        }
        StringBuffer code = new StringBuffer();
        code.append("java.lang.Object[] values = new java.lang.Object[" +variables.size()+ "];\n");
        for (int i = 0; i < variables.size(); i++) {
            Entry e = (Entry) variables.get(i);
            code.append("values[" + i + "] = ");
            if (BOOLEAN.equals(e.type)) {
                code.append("new java.lang.Boolean(" + e.name + ");\n");
            } else {
                code.append(e.name + ";\n");
            }
        }
        code.append(var + ".push(values);\n");
        RacNode node = RacParser.parseStatement(code.toString());
        return node.incrIndent();
    }

    RacNode restoreCode(/*@ non_null @*/ String var) {
        if (variables.isEmpty()) {
            return null;
        }
        StringBuffer code = new StringBuffer();
        code.append("java.lang.Object[] values = (java.lang.Object[])" + var + ".pop();\n");
        int j = 0;
        for (Iterator i = variables.iterator(); i.hasNext(); j++) {
            Entry e = (Entry) i.next();
            code.append(e.name + " = (");
            if (BOOLEAN.equals(e.type)) {
                code.append("(java.lang.Boolean) values[" + j + "]).booleanValue();\n");
            } else {
                code.append(e.type + ") values[" + j + "];\n");
            }
        }
        RacNode node = RacParser.parseStatement(code.toString());
        return node.incrIndent();
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** A data structure class to hold information about a field. */
    static class Entry {
        Entry(boolean isStatic, String type, String name, String value) {
            this.isStatic = isStatic;
            this.type = type;
            this.name = name;
            this.value = value;
        }

        boolean isStatic;
        String type;
        String name;
        String value;

        /** Returns the type of this variable declaration. */
        public String type() {
            return type;
        }

        /** Returns the name of this variable declaration. */
        public String name() {
            return name;
        }

        /** Returns a sting representation of this entry. The
         * returned string has the form:
         * <code>[static] T x = v;</code>*/
        public String toString() {
            return (isStatic? "static " : "") + "transient " + type + " " +
                name + " = " + value + ";";
        }
    }

    private ArrayList variables = new ArrayList();

    private final static String NULL = "null";
    private final static String BOOLEAN = "boolean";
    private final static String FALSE = "false";
    private final static String PREFIX = "c";
}
