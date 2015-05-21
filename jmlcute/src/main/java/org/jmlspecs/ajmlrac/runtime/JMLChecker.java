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
 * $Id: AssertionMethod.java,v 1.0 2009/01/15 05:11:33 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: JMLChecker.java,v 1.25 2007/02/03 02:04:50 delara Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac.runtime;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Stack;
import java.util.Vector;

import org.jmlspecs.ajmlrac.RacConstants;
import org.jmlspecs.checker.Constants;


/**
 * A class to set various runtime options and to check and report
 * runtime assertion violations.
 * <p/>
 * part of the original JMLChecker.java file by Yoonsik Cheon
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */

public class JMLChecker implements JMLOption {

    // ----------------------------------------------------------------------
    // STATIC METHODS
    // ----------------------------------------------------------------------

    /**
     * Returns true only if the given class, <code>clazz</code>, is
     * compiled with runtime assertion check code.
     */
    public static boolean isRACCompiled(/*@ non_null @*/ Class clazz) {
        try {
            Class.forName(RacConstants.TN_TEMPORARY_ASPECT_FILE_NAME + clazz.getCanonicalName().replace(".", "_"));
            return true;
        } catch (SecurityException e) {
            return false;
        } catch (ClassNotFoundException e) {
            return false;
        }
    }

    /**
     * Sets the global runtime assertion check level to the level
     * <code>l</code>.
     * <p/>
     * <pre><jml>
     * normal_behavior
     *   requires l == NONE || l == PRECONDITIONS_ONLY || l == ALL;
     *   assignable level;
     *   ensures level == l;
     * </jml></pre>
     */
    public static void setLevel(int l) {
        level = l;
    }

    /**
     * Returns the current global runtime assertion check level.  The
     * returned value is <code>NONE</code>,
     * <code>PRECONDITIONS_ONLY</code>, or <code>ALL</code>.
     * <p/>
     * <pre><jml>
     * normal_behavior
     *   assignable \nothing;
     *   ensures \result == level;
     * </jml></pre>
     */
    public static int getLevel() {
        return level;
    }

    /**
     * Returns the result of invoking the <code>toString</code> method
     * to the argument, <code>obj</code>. If the argument is null, "null"
     * is returned. If the invocation encounters an exception,
     * "UNKNOWN" is returned; otherwise, the result of invocation
     * is returned.
     */
    public static /*@ non_null @*/ String toString(Object obj) {
        if (obj == null) {
            return "null";
        }

        String result = "<UNKNOWN-to-JML>";
        try {
            result = obj.toString();
        } catch (java.lang.Throwable e1) {
            String addr = "<UNKNOWN-to-JML>";
            try {
                addr = "" + obj.hashCode();
            } catch (java.lang.Throwable e2) {
            }
            result = obj.getClass().getName() + "@" + addr;
        }
        return result;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(boolean i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(byte i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(char i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(int i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(short i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(long i) {
        return "" + i;
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(float value) {
        if (value == Float.POSITIVE_INFINITY) {
            return "java.lang.Float.POSITIVE_INFINITY";
        } else if (value == Float.NEGATIVE_INFINITY) {
            return "java.lang.Float.NEGATIVE_INFINITY";
        } else if (Float.isNaN(value)) {
            return "java.lang.Float.NaN";
        } else if (value == 0.0F && (new Float(value).equals(new Float("-0.0")))) {
            return "-0.0F";
        } else if (value == Float.MAX_VALUE) {
            return "java.lang.Float.MAX_VALUE";
        } else if (value == Float.MIN_VALUE) {
            return "java.lang.Float.MIN_VALUE";
        } else if (value == 0.0F) {
            return "+0.0F";
        } else {
            return value + "F";
        }
    }

    /**
     * Returns the string representation of the given argument.
     */
    public static /*@ non_null @*/ String toString(double value) {
        if (value == Double.POSITIVE_INFINITY) {
            return "java.lang.Double.POSITIVE_INFINITY";
        } else if (value == Double.NEGATIVE_INFINITY) {
            return "java.lang.Double.NEGATIVE_INFINITY";
        } else if (Double.isNaN(value)) {
            return "java.lang.Double.NaN";
        } else if (value == Double.MAX_VALUE) {
            return "java.lang.Double.MAX_VALUE";
        } else if (value == Double.MIN_VALUE) {
            return "java.lang.Double.MIN_VALUE";
        } else if (value == 0.0D && (new Double(value).equals(new Double("-0.0")))) {
            return "-0.0D";
        } else if (value == 0.0D) {
            return "+0.0D";
        } else {
            return value + "D";
        }
    }

    public static void checkInvariant(boolean pred, String invErrorMsg, long visibility) {
        JMLChecker.checkInvariantHelper(pred, invErrorMsg, visibility);
    }

    public static void checkConstraint(boolean pred, String constErrorMsg, long visibility) {
        JMLChecker.checkConstraintHelper(pred, constErrorMsg, visibility);
    }

    public static void checkPrecondition(boolean pred, boolean canThrow,
                                         String preErrorMsg, long visibility,
                                         String methodName) {
        JMLChecker.checkPreconditionHelper(pred, canThrow, preErrorMsg, visibility, methodName);
    }

    public static void checkNormalPostcondition(boolean pred,
                                                String nPostErrorMsg, long visibility,
                                                String methodName) {
        JMLChecker.checkNormalPostconditionHelper(pred, nPostErrorMsg,
                visibility, methodName);
    }

    public static void checkExceptionalPostcondition(boolean pred,
                                                     String xPostErrorMsg, String xKind, boolean isXCS, long visibility, String methodName, Throwable cause) {
        JMLChecker.checkExceptionalPostconditionHelper(pred, xPostErrorMsg, xKind, isXCS,
                visibility, methodName, cause);
    }

    // multiple spec case checking methods
    public static void checkInvariantMultipleSpecCaseChecking(boolean pred, String invErrorMsg, long visibility) {
        JMLChecker.checkInvariantMultipleSpecCaseCheckingHelper(pred, invErrorMsg, visibility);
    }

    public static void checkConstraintMultipleSpecCaseChecking(boolean pred, String constErrorMsg, long visibility) {
        JMLChecker.checkConstraintMultipleSpecCaseCheckingHelper(pred, constErrorMsg, visibility);
    }


    public static void checkNPostMultipleSpecCaseChecking(boolean pred,
                                                          String nPostErrorMsg, long visibility, String methodName) {
        JMLChecker.checkNPostMultipleSpecCaseCheckingHelper(pred,
                nPostErrorMsg, visibility, methodName);
    }

    public static void checkXPostMultipleSpecCaseChecking(boolean pred,
                                                          String xPostErrorMsg, String xKind, boolean isXCS, long visibility,
                                                          String methodName, Throwable cause) {
        JMLChecker.checkXPostMultipleSpecCaseCheckingHelper(pred,
                xPostErrorMsg, xKind, isXCS, visibility, methodName, cause);
    }

    // helpers
    private static void checkInvariantHelper(boolean pred, String invErrorMsg, long visibility) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            JMLChecker.throwInvariantError(invErrorMsg, visibility);
        }
    }

    private static void checkConstraintHelper(boolean pred, String constErrorMsg, long visibility) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            JMLChecker.throwConstraintError(constErrorMsg, visibility);
        }
    }

    private static void checkInvariantMultipleSpecCaseCheckingHelper(boolean pred, String invErrorMsg, long visibility) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            JMLChecker.recordInvariantError(invErrorMsg, visibility);
        } else {
            JMLChecker.recordInvariantSat(invErrorMsg);
        }
    }

    private static void checkConstraintMultipleSpecCaseCheckingHelper(boolean pred, String constErrorMsg, long visibility) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            JMLChecker.recordConstraintError(constErrorMsg, visibility);
        } else {
            JMLChecker.recordConstraintSat(constErrorMsg);
        }
    }

    private static void checkPreconditionHelper(boolean pred, boolean canThrow,
                                                String preErrorMsg, long visibility, String methodName) {
        if (!pred) {
            if (canThrow) {
                JMLChecker.throwPreconditionError(preErrorMsg, visibility, methodName);
            } else {
                JMLChecker.recordPreconditionError(preErrorMsg, visibility, methodName);
            }
        } else {
            if (!canThrow) {
                JMLSatisfiedPrecondition jsp =
                        new JMLSatisfiedPrecondition("satified precondition of" + methodName + " with visibility = " + visibility, methodName, visibility);
                JMLChecker.checkedMethPreconditions.add(jsp);
            }
        }
    }

    private static void checkNormalPostconditionHelper(boolean pred,
                                                       String nPostErrorMsg, long visibility, String methodName) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            throwNormalPostconditionError(nPostErrorMsg, visibility, methodName);
        }
    }

    private static void checkExceptionalPostconditionHelper(boolean pred,
                                                            String xPostErrorMsg, String xKind, boolean isXCS, long visibility, String methodName, Throwable cause) {
        if (isXCS && xKind.equals("jml$e")) {
            if (!pred) {
                JMLChecker.hasAnyJMLError = true;
                recordExceptionalPostconditionSignalsOnlyError(xPostErrorMsg, visibility, methodName, cause);
            } else {
                JMLSatisfiedXPostconditionSignalsOnly jsp =
                        new JMLSatisfiedXPostconditionSignalsOnly("satified signals_only of" + methodName + " with visibility = " + visibility, methodName, visibility);
                JMLChecker.xPostconditionSignalsOnlySat.add(jsp);
            }
        } else {
            if (!pred) {
                JMLChecker.hasAnyJMLError = true;
                throwExceptionalPostconditionError(xPostErrorMsg, visibility, methodName, cause);
            }
        }
    }

    private static void checkNPostMultipleSpecCaseCheckingHelper(boolean pred,
                                                                 String nPostErrorMsg, long visibility, String methodName) {
        if (!pred) {
            JMLChecker.hasAnyJMLError = true;
            recordNormalPostconditionError(nPostErrorMsg, visibility, methodName);
        } else {
            recordNormalPostconditionSat(nPostErrorMsg);
        }
    }

    private static void checkXPostMultipleSpecCaseCheckingHelper(boolean pred,
                                                                 String xPostErrorMsg, String xKind, boolean isXCS, long visibility, String methodName, Throwable cause) {
        if (isXCS && xKind.equals("jml$e")) {
            if (!pred) {
                JMLChecker.hasAnyJMLError = true;
                recordExceptionalPostconditionSignalsOnlyError(xPostErrorMsg, visibility, methodName, cause);
            } else {
                JMLSatisfiedXPostconditionSignalsOnly jsp =
                        new JMLSatisfiedXPostconditionSignalsOnly("satified signals_only of" + methodName + " with visibility = " + visibility, methodName, visibility);
                JMLChecker.xPostconditionSignalsOnlySat.add(jsp);
            }
        } else {
            if (!pred) {
                JMLChecker.hasAnyJMLError = true;
                recordExceptionalPostconditionError(xPostErrorMsg, visibility, methodName, cause);
            } else {
                recordExceptionalPostconditionSat(xPostErrorMsg);
            }
        }
    }

    // throw methods
    private static void throwInvariantError(String invErrorMsg, long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            throw new JMLPublicInvariantError(invErrorMsg);
        } else if (visibility == Constants.ACC_PROTECTED) {
            throw new JMLProtectedInvariantError(invErrorMsg);
        } else if (visibility == 0L) { //default
            throw new JMLDefaultInvariantError(invErrorMsg);
        } else if (visibility == Constants.ACC_PRIVATE) {
            throw new JMLPrivateInvariantError(invErrorMsg);
        } else {
            throw new JMLInvariantError(invErrorMsg);
        }
    }

    // throw methods
    private static void throwConstraintError(String constErrorMsg, long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            throw new JMLPublicHistoryConstraintError(constErrorMsg);
        } else if (visibility == Constants.ACC_PROTECTED) {
            throw new JMLProtectedHistoryConstraintError(constErrorMsg);
        } else if (visibility == 0L) { //default
            throw new JMLDefaultHistoryConstraintError(constErrorMsg);
        } else if (visibility == Constants.ACC_PRIVATE) {
            throw new JMLPrivateHistoryConstraintError(constErrorMsg);
        } else {
            throw new JMLHistoryConstraintError(constErrorMsg);
        }
    }

    private static void throwPreconditionError(String preErrorMsg, long visibility, String methodName) {
        if (visibility == Constants.ACC_PUBLIC) {
            throw new JMLEntryPublicPreconditionError(preErrorMsg, methodName);
        } else if (visibility == Constants.ACC_PROTECTED) {
            throw new JMLEntryProtectedPreconditionError(preErrorMsg, methodName);
        } else if (visibility == 0L) { //default
            throw new JMLEntryDefaultPreconditionError(preErrorMsg, methodName);
        } else if (visibility == Constants.ACC_PRIVATE) {
            throw new JMLEntryPrivatePreconditionError(preErrorMsg, methodName);
        } else {
            throw new JMLEntryPreconditionError(preErrorMsg, methodName);
        }
    }

    private static void throwNormalPostconditionError(String nPostErrorMsg,
                                                      long visibility, String methodName) {
        if (visibility == Constants.ACC_PUBLIC) {
            throw new JMLExitPublicNormalPostconditionError(nPostErrorMsg, methodName);
        } else if (visibility == Constants.ACC_PROTECTED) {
            throw new JMLExitProtectedNormalPostconditionError(nPostErrorMsg, methodName);
        } else if (visibility == 0L) { // default
            throw new JMLExitDefaultNormalPostconditionError(nPostErrorMsg, methodName);
        } else if (visibility == Constants.ACC_PRIVATE) {
            throw new JMLExitPrivateNormalPostconditionError(nPostErrorMsg, methodName);
        } else {
            throw new JMLExitNormalPostconditionError(nPostErrorMsg, methodName);
        }
    }

    private static void throwExceptionalPostconditionError(String xPostErrorMsg,
                                                           long visibility, String methodName, Throwable cause) {
        if (visibility == Constants.ACC_PUBLIC) {
            throw new JMLExitPublicExceptionalPostconditionError(xPostErrorMsg, methodName, cause);
        } else if (visibility == Constants.ACC_PROTECTED) {
            throw new JMLExitProtectedExceptionalPostconditionError(xPostErrorMsg, methodName, cause);
        } else if (visibility == 0L) { // default
            throw new JMLExitDefaultExceptionalPostconditionError(xPostErrorMsg, methodName, cause);
        } else if (visibility == Constants.ACC_PRIVATE) {
            throw new JMLExitPrivateExceptionalPostconditionError(xPostErrorMsg, methodName, cause);
        } else {
            throw new JMLExitExceptionalPostconditionError(xPostErrorMsg, methodName, cause);
        }
    }

    // rethrow methods
    public static void rethrowJMLAssertionError(Throwable rac$e, String methodName) {
        if (rac$e instanceof JMLAssertionError) {
            if (((JMLAssertionError) rac$e).methodName.equals(methodName)) {
                throw (JMLAssertionError) rac$e;
            } else {
                if (rac$e instanceof JMLPreconditionError) {
                    if (rac$e instanceof JMLEntryPublicPreconditionError) {
                        throw new JMLInternalPublicPreconditionError(rac$e);
                    } else if (rac$e instanceof JMLEntryProtectedPreconditionError) {
                        throw new JMLInternalProtectedPreconditionError(rac$e);
                    } else if (rac$e instanceof JMLEntryDefaultPreconditionError) {
                        throw new JMLInternalDefaultPreconditionError(rac$e);
                    } else if (rac$e instanceof JMLEntryPrivatePreconditionError) {
                        throw new JMLInternalPrivatePreconditionError(rac$e);
                    } else if (rac$e instanceof JMLEntryPreconditionError) {
                        throw new JMLInternalPreconditionError(rac$e);
                    }
                } else if (rac$e instanceof JMLNormalPostconditionError) {
                    if (rac$e instanceof JMLExitPublicNormalPostconditionError) {
                        throw new JMLInternalPublicNormalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitProtectedNormalPostconditionError) {
                        throw new JMLInternalProtectedNormalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitDefaultNormalPostconditionError) {
                        throw new JMLInternalDefaultNormalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitPrivateNormalPostconditionError) {
                        throw new JMLInternalPrivateNormalPostconditionError(rac$e);
                    } else {
                        throw new JMLInternalNormalPostconditionError(rac$e);
                    }
                } else if (rac$e instanceof JMLExceptionalPostconditionError) {
                    if (rac$e instanceof JMLExitPublicExceptionalPostconditionError) {
                        throw new JMLInternalPublicExceptionalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitProtectedExceptionalPostconditionError) {
                        throw new JMLInternalProtectedExceptionalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitDefaultExceptionalPostconditionError) {
                        throw new JMLInternalDefaultExceptionalPostconditionError(rac$e);
                    } else if (rac$e instanceof JMLExitPrivateExceptionalPostconditionError) {
                        throw new JMLInternalPrivateExceptionalPostconditionError(rac$e);
                    } else {
                        throw new JMLInternalExceptionalPostconditionError(rac$e);
                    }
                } else {
                    throw (JMLAssertionError) rac$e;
                }
            }
        }
    }

    public static void rethrowUncheckedException(Throwable rac$e) {
        if (rac$e instanceof java.lang.RuntimeException) {
            throw (java.lang.RuntimeException) rac$e;
        } else if (rac$e instanceof java.lang.Error) {
            throw (java.lang.Error) rac$e;
        }
    }

    // record methods
    private static void recordInvariantError(String invError, long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            if (JMLChecker.invariantError != null) {
                JMLChecker.invariantError = new JMLPublicInvariantError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.invariantError.toString());
            } else {
                JMLChecker.invariantError = new JMLPublicInvariantError(
                        invError);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            if (JMLChecker.invariantError != null) {
                JMLChecker.invariantError = new JMLProtectedInvariantError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.invariantError.toString());
            } else {
                JMLChecker.invariantError = new JMLProtectedInvariantError(
                        invError);
            }
        } else if (visibility == 0L) { // default
            if (JMLChecker.invariantError != null) {
                JMLChecker.invariantError = new JMLDefaultInvariantError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.invariantError.toString());
            } else {
                JMLChecker.invariantError = new JMLDefaultInvariantError(
                        invError);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            if (JMLChecker.invariantError != null) {
                JMLChecker.invariantError = new JMLPrivateInvariantError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.invariantError.toString());
            } else {
                JMLChecker.invariantError = new JMLPrivateInvariantError(
                        invError);
            }
        } else {
            if (JMLChecker.invariantError != null) {
                JMLChecker.invariantError = new JMLInvariantError(invError
                        + "\n" + "[which is joined locally or inherited by \'also\'] "
                        + JMLChecker.invariantError.toString());
            } else {
                JMLChecker.invariantError = new JMLInvariantError(invError);
            }
        }
    }

    private static void recordConstraintError(String invError, long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            if (JMLChecker.constraintError != null) {
                JMLChecker.constraintError = new JMLPublicHistoryConstraintError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.constraintError.toString());
            } else {
                JMLChecker.constraintError = new JMLPublicHistoryConstraintError(
                        invError);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            if (JMLChecker.constraintError != null) {
                JMLChecker.constraintError = new JMLProtectedHistoryConstraintError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.constraintError.toString());
            } else {
                JMLChecker.constraintError = new JMLProtectedHistoryConstraintError(
                        invError);
            }
        } else if (visibility == 0L) { // default
            if (JMLChecker.constraintError != null) {
                JMLChecker.constraintError = new JMLDefaultHistoryConstraintError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.constraintError.toString());
            } else {
                JMLChecker.constraintError = new JMLDefaultHistoryConstraintError(
                        invError);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            if (JMLChecker.constraintError != null) {
                JMLChecker.constraintError = new JMLPrivateHistoryConstraintError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.constraintError.toString());
            } else {
                JMLChecker.constraintError = new JMLPrivateHistoryConstraintError(
                        invError);
            }
        } else {
            if (JMLChecker.constraintError != null) {
                JMLChecker.constraintError = new JMLHistoryConstraintError(
                        invError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + JMLChecker.constraintError.toString());
            } else {
                JMLChecker.constraintError = new JMLHistoryConstraintError(
                        invError);
            }
        }
    }

    private static JMLPreconditionError getMethPreconditionError(String methodName) {
        JMLPreconditionError result = null;
        for (Iterator iterator = JMLChecker.checkedMethPreconditions.iterator(); iterator.hasNext(); ) {
            JMLPreconditionError currentMethPreError = (JMLPreconditionError) iterator.next();
            if (currentMethPreError instanceof JMLEntryPublicPreconditionError) {
                if (methodName.equals(currentMethPreError.methodName)) {
                    result = currentMethPreError;
                    break;
                }
            }
            if (currentMethPreError instanceof JMLEntryProtectedPreconditionError) {
                if (methodName.equals(currentMethPreError.methodName)) {
                    result = currentMethPreError;
                    break;
                }
            }

            if (currentMethPreError instanceof JMLEntryDefaultPreconditionError) {
                if (methodName.equals(currentMethPreError.methodName)) {
                    result = currentMethPreError;
                    break;
                }
            }
            if (currentMethPreError instanceof JMLEntryPrivatePreconditionError) {
                if (methodName.equals(currentMethPreError.methodName)) {
                    result = currentMethPreError;
                    break;
                }
            }
            if (currentMethPreError instanceof JMLEntryPreconditionError) {
                if (methodName.equals(currentMethPreError.methodName)) {
                    result = currentMethPreError;
                    break;
                }
            }
        }
        return result;
    }

    private static void recordPreconditionError(String preErrorMsg,
                                                long visibility, String methodName) {
        JMLPreconditionError jpe = null;

        if (visibility == Constants.ACC_PUBLIC) {
            jpe = JMLChecker.getMethPreconditionError(methodName);
            if (jpe != null) {
                jpe = new JMLEntryPublicPreconditionError(
                        preErrorMsg + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + jpe.toString(), methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            } else {
                jpe = new JMLEntryPublicPreconditionError(preErrorMsg, methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            jpe = JMLChecker.getMethPreconditionError(methodName);
            if (jpe != null) {
                jpe = new JMLEntryProtectedPreconditionError(
                        preErrorMsg + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + jpe.toString(), methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            } else {
                jpe = new JMLEntryProtectedPreconditionError(preErrorMsg, methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            }
        } else if (visibility == 0L) { // default
            jpe = JMLChecker.getMethPreconditionError(methodName);
            if (jpe != null) {
                jpe = new JMLEntryDefaultPreconditionError(
                        preErrorMsg + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + jpe.toString(), methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            } else {
                jpe = new JMLEntryDefaultPreconditionError(preErrorMsg, methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            jpe = JMLChecker.getMethPreconditionError(methodName);
            if (jpe != null) {
                jpe = new JMLEntryPrivatePreconditionError(
                        preErrorMsg + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + jpe.toString(), methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            } else {
                jpe = new JMLEntryPrivatePreconditionError(preErrorMsg, methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            }
        } else {
            jpe = JMLChecker.getMethPreconditionError(methodName);
            if (jpe != null) {
                jpe = new JMLEntryPreconditionError(
                        preErrorMsg + "\n" + "[which is joined locally or inherited by \'also\'] "
                                + jpe.toString(), methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            } else {
                jpe = new JMLEntryPreconditionError(preErrorMsg, methodName);
                JMLChecker.checkedMethPreconditions.push(jpe);
            }
        }
    }

    private static void recordNormalPostconditionError(String nPostError,
                                                       long visibility, String methodName) {
        if (visibility == Constants.ACC_PUBLIC) {
            if (JMLChecker.nPostconditionError != null) {
                if (((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.nPostconditionError = new JMLExitPublicNormalPostconditionError(
                            nPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.nPostconditionError.toString(), methodName);
                }
            } else {
                JMLChecker.nPostconditionError = new JMLExitPublicNormalPostconditionError(
                        nPostError, methodName);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            if (JMLChecker.nPostconditionError != null) {
                if (((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.nPostconditionError = new JMLExitProtectedNormalPostconditionError(
                            nPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.nPostconditionError.toString(), methodName);
                }
            } else {
                JMLChecker.nPostconditionError = new JMLExitProtectedNormalPostconditionError(
                        nPostError, methodName);
            }
        } else if (visibility == 0L) { // default
            if (JMLChecker.nPostconditionError != null) {
                if (((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.nPostconditionError = new JMLExitDefaultNormalPostconditionError(
                            nPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.nPostconditionError.toString(), methodName);
                }
            } else {
                JMLChecker.nPostconditionError = new JMLExitDefaultNormalPostconditionError(
                        nPostError, methodName);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            if (JMLChecker.nPostconditionError != null) {
                if (((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.nPostconditionError = new JMLExitPrivateNormalPostconditionError(
                            nPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.nPostconditionError.toString(), methodName);
                }
            } else {
                JMLChecker.nPostconditionError = new JMLExitPrivateNormalPostconditionError(
                        nPostError, methodName);
            }
        } else {
            if (JMLChecker.nPostconditionError != null) {
                if (((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.nPostconditionError = new JMLExitNormalPostconditionError(
                            nPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.nPostconditionError.toString(), methodName);
                }
            } else {
                JMLChecker.nPostconditionError = new JMLExitNormalPostconditionError(
                        nPostError, methodName);
            }
        }
    }

    private static void recordExceptionalPostconditionError(String xPostError,
                                                            long visibility, String methodName, Throwable cause) {
        if (visibility == Constants.ACC_PUBLIC) {
            if (JMLChecker.xPostconditionError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionError = new JMLExitPublicExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionError = new JMLExitPublicExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            if (JMLChecker.xPostconditionError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionError = new JMLExitProtectedExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionError = new JMLExitProtectedExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == 0L) { // default
            if (JMLChecker.xPostconditionError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionError = new JMLExitDefaultExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionError = new JMLExitDefaultExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            if (JMLChecker.xPostconditionError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionError = new JMLExitPrivateExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionError = new JMLExitPrivateExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else {
            if (JMLChecker.xPostconditionError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionError = new JMLExitExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionError = new JMLExitExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        }
    }

    private static void recordExceptionalPostconditionSignalsOnlyError(String xPostError,
                                                                       long visibility, String methodName, Throwable cause) {
        if (visibility == Constants.ACC_PUBLIC) {
            if (JMLChecker.xPostconditionSignalsOnlyError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionSignalsOnlyError = new JMLExitPublicExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionSignalsOnlyError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionSignalsOnlyError = new JMLExitPublicExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == Constants.ACC_PROTECTED) {
            if (JMLChecker.xPostconditionSignalsOnlyError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionSignalsOnlyError = new JMLExitProtectedExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionSignalsOnlyError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionSignalsOnlyError = new JMLExitProtectedExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == 0L) { // default
            if (JMLChecker.xPostconditionSignalsOnlyError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionSignalsOnlyError = new JMLExitDefaultExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionSignalsOnlyError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionSignalsOnlyError = new JMLExitDefaultExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else if (visibility == Constants.ACC_PRIVATE) {
            if (JMLChecker.xPostconditionSignalsOnlyError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionSignalsOnlyError = new JMLExitPrivateExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionSignalsOnlyError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionSignalsOnlyError = new JMLExitPrivateExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        } else {
            if (JMLChecker.xPostconditionSignalsOnlyError != null) {
                if (((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName.equals(methodName)) {
                    JMLChecker.xPostconditionSignalsOnlyError = new JMLExitExceptionalPostconditionError(
                            xPostError + "\n" + "[which is joined locally or inherited by \'also\'] "
                                    + JMLChecker.xPostconditionSignalsOnlyError.toString(), methodName, cause);
                }
            } else {
                JMLChecker.xPostconditionSignalsOnlyError = new JMLExitExceptionalPostconditionError(
                        xPostError, methodName, cause);
            }
        }
    }

    private static void recordNormalPostconditionSat(String nPostSat) {
        JMLChecker.nPostconditionSat.add(nPostSat);
    }

    private static void recordExceptionalPostconditionSat(String xPostSat) {
        JMLChecker.xPostconditionSat.add(xPostSat);
    }

    private static void recordExceptionalPostconditionSingalsOnlySat(String xPostSat) {
        JMLChecker.xPostconditionSignalsOnlySat.add(xPostSat);
    }

    private static void recordInvariantSat(String invSat) {
        JMLChecker.invariantSat.add(invSat);
    }

    private static void recordConstraintSat(String invSat) {
        JMLChecker.constraintSat.add(invSat);
    }

    // hasAnyThrown
    public static void hasAnyThrownInvariant() {
        if (JMLChecker.invariantError != null) {
            String errorMsg = JMLChecker.invariantError.toString();
            if (invariantSat.size() > 0) {
                errorMsg += "\n" + "[also satisfied invariants] ";
                for (int i = 0; i < invariantSat.size(); i++) {
                    String efectiveInv = (String) invariantSat.get(i);
                    errorMsg += "\n" + "[satisfied] " + efectiveInv;
                }
            }

            invariantSat = new Vector();
            if (JMLChecker.invariantError instanceof JMLPublicInvariantError) {
                throw new JMLPublicInvariantError(errorMsg);
            } else if (JMLChecker.invariantError instanceof JMLProtectedInvariantError) {
                throw new JMLProtectedInvariantError(errorMsg);
            } else if (JMLChecker.invariantError instanceof JMLDefaultInvariantError) {
                throw new JMLDefaultInvariantError(errorMsg);
            } else if (JMLChecker.invariantError instanceof JMLPrivateInvariantError) {
                throw new JMLPrivateInvariantError(errorMsg);
            } else if (JMLChecker.invariantError instanceof JMLInvariantError) {
                throw new JMLInvariantError(errorMsg);
            }
        }
    }

    public static void hasAnyThrownConstraint() {
        if (JMLChecker.constraintError != null) {
            String errorMsg = JMLChecker.constraintError.toString();
            if (constraintSat.size() > 0) {
                errorMsg += "\n" + "[also satisfied constraints] ";
                for (int j = 0; j < constraintSat.size(); j++) {
                    String efectiveConst = (String) constraintSat.get(j);
                    errorMsg += "\n" + "[satisfied] " + efectiveConst;
                }

                constraintSat = new Vector();
            }
            if (JMLChecker.constraintError instanceof JMLPublicHistoryConstraintError) {
                throw new JMLPublicHistoryConstraintError(errorMsg);
            } else if (JMLChecker.constraintError instanceof JMLProtectedHistoryConstraintError) {
                throw new JMLProtectedHistoryConstraintError(errorMsg);
            } else if (JMLChecker.constraintError instanceof JMLDefaultHistoryConstraintError) {
                throw new JMLDefaultHistoryConstraintError(errorMsg);
            } else if (JMLChecker.constraintError instanceof JMLDefaultHistoryConstraintError) {
                throw new JMLDefaultHistoryConstraintError(errorMsg);
            } else if (JMLChecker.constraintError instanceof JMLHistoryConstraintError) {
                throw new JMLHistoryConstraintError(errorMsg);
            }
        }
    }

    private static boolean canThrowPreconditionError(long visibility, String methodName, Vector preErrors) {
        boolean result = true;
        for (Iterator iterator = preErrors.iterator(); iterator.hasNext(); ) {
            JMLPreconditionError currentPreError = (JMLPreconditionError) iterator.next();
            if (currentPreError instanceof JMLSatisfiedPrecondition) {
                JMLSatisfiedPrecondition jsp = (JMLSatisfiedPrecondition) currentPreError;
                if ((methodName.equals(jsp.methodName)) && (visibility == jsp.visibility)) {
                    result = false;
                }
            }
        }
        return result;
    }

    private static boolean canThrowXPostconditionSignalsOnlyError(long visibility, String methodName) {
        boolean result = true;
        for (Iterator iterator = xPostconditionSignalsOnlySat.iterator(); iterator.hasNext(); ) {
            JMLSatisfiedXPostconditionSignalsOnly currentXPostError = (JMLSatisfiedXPostconditionSignalsOnly) iterator.next();
            if (currentXPostError instanceof JMLSatisfiedXPostconditionSignalsOnly) {
                JMLSatisfiedXPostconditionSignalsOnly jsp = (JMLSatisfiedXPostconditionSignalsOnly) currentXPostError;
                if ((methodName.equals(jsp.methodName)) && (visibility == jsp.visibility)) {
                    result = false;
                }
            }
        }
        return result;
    }

    public static void hasAnyThrownPrecondition() {
        Vector preErrors = new Vector();
        while (JMLChecker.checkedMethPreconditions.size() > 0) {
            preErrors.add(JMLChecker.checkedMethPreconditions.pop());
        }
        for (Iterator iterator = preErrors.iterator(); iterator.hasNext(); ) {
            JMLPreconditionError currentPreError = (JMLPreconditionError) iterator.next();
            if (currentPreError instanceof JMLEntryPreconditionError) {
                if (currentPreError instanceof JMLEntryPublicPreconditionError) {
                    if (JMLChecker.canThrowPreconditionError(Constants.ACC_PUBLIC, currentPreError.methodName, preErrors)) {
                        throw (JMLPreconditionError) currentPreError;
                    }
                } else if (currentPreError instanceof JMLEntryProtectedPreconditionError) {
                    if (JMLChecker.canThrowPreconditionError(Constants.ACC_PROTECTED, currentPreError.methodName, preErrors)) {
                        throw (JMLPreconditionError) currentPreError;
                    }
                } else if (currentPreError instanceof JMLEntryDefaultPreconditionError) {
                    if (JMLChecker.canThrowPreconditionError(0L, currentPreError.methodName, preErrors)) {
                        throw (JMLPreconditionError) currentPreError;
                    }
                } else if (currentPreError instanceof JMLEntryPrivatePreconditionError) {
                    if (JMLChecker.canThrowPreconditionError(Constants.ACC_PRIVATE, currentPreError.methodName, preErrors)) {
                        throw (JMLPreconditionError) currentPreError;
                    }
                } else {
                    if (JMLChecker.canThrowPreconditionError(-1, currentPreError.methodName, preErrors)) {
                        throw (JMLPreconditionError) currentPreError;
                    }
                }
            }
        }
    }

    public static void hasAnyThrownNormalPostcondition() {
        if (JMLChecker.nPostconditionError != null) {
            String errorMsg = JMLChecker.nPostconditionError.toString();
            String methodName = ((JMLNormalPostconditionError) JMLChecker.nPostconditionError).methodName;
            if (nPostconditionSat.size() > 0) {
                errorMsg += "\n" + "[also satisfied normal postconditions] ";
                for (int i = 0; i < nPostconditionSat.size(); i++) {
                    String speccase = (String) nPostconditionSat.get(i);
                    errorMsg += "\n" + "[satisfied] " + speccase;
                }
            }

            nPostconditionSat = new Vector();
            if (JMLChecker.nPostconditionError instanceof JMLExitPublicNormalPostconditionError) {
                throw new JMLExitPublicNormalPostconditionError(errorMsg, methodName);
            } else if (JMLChecker.nPostconditionError instanceof JMLExitProtectedNormalPostconditionError) {
                throw new JMLExitProtectedNormalPostconditionError(errorMsg, methodName);
            } else if (JMLChecker.nPostconditionError instanceof JMLExitDefaultNormalPostconditionError) {
                throw new JMLExitDefaultNormalPostconditionError(errorMsg, methodName);
            } else if (JMLChecker.nPostconditionError instanceof JMLExitPrivateNormalPostconditionError) {
                throw new JMLExitPrivateNormalPostconditionError(errorMsg, methodName);
            } else if (JMLChecker.nPostconditionError instanceof JMLExitNormalPostconditionError) {
                throw new JMLExitNormalPostconditionError(errorMsg, methodName);
            }

            if (JMLChecker.nPostconditionError instanceof JMLInternalPublicNormalPostconditionError) {
                throw new JMLInternalPublicNormalPostconditionError(errorMsg);
            } else if (JMLChecker.nPostconditionError instanceof JMLInternalProtectedNormalPostconditionError) {
                throw new JMLInternalProtectedNormalPostconditionError(errorMsg);
            } else if (JMLChecker.nPostconditionError instanceof JMLInternalDefaultNormalPostconditionError) {
                throw new JMLInternalDefaultNormalPostconditionError(errorMsg);
            } else if (JMLChecker.nPostconditionError instanceof JMLInternalPrivateNormalPostconditionError) {
                throw new JMLInternalPrivateNormalPostconditionError(errorMsg);
            } else if (JMLChecker.nPostconditionError instanceof JMLInternalNormalPostconditionError) {
                throw new JMLInternalNormalPostconditionError(errorMsg);
            }
        }
    }

    public static void hasAnyThrownExceptionalPostcondition() {
        if (JMLChecker.xPostconditionError != null) {
            String errorMsg = JMLChecker.xPostconditionError.toString();
            String methodName = ((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).methodName;
            Throwable cause = ((JMLExceptionalPostconditionError) JMLChecker.xPostconditionError).getRacCause();
            if (xPostconditionSat.size() > 0) {
                errorMsg += "\n" + "[also satisfied exceptional postconditions] ";
                for (int i = 0; i < xPostconditionSat.size(); i++) {
                    String speccase = (String) xPostconditionSat.get(i);
                    errorMsg += "\n" + "[satisfied] " + speccase;
                }
            }

            xPostconditionSat = new Vector();
            if (JMLChecker.xPostconditionError instanceof JMLExitPublicExceptionalPostconditionError) {
                throw new JMLExitPublicExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLExitProtectedExceptionalPostconditionError) {
                throw new JMLExitProtectedExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLExitDefaultExceptionalPostconditionError) {
                throw new JMLExitDefaultExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLExitPrivateExceptionalPostconditionError) {
                throw new JMLExitPrivateExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLExitExceptionalPostconditionError) {
                throw new JMLExitExceptionalPostconditionError(errorMsg, methodName, cause);
            }

            if (JMLChecker.xPostconditionError instanceof JMLInternalPublicExceptionalPostconditionError) {
                throw new JMLInternalPublicExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLInternalProtectedExceptionalPostconditionError) {
                throw new JMLInternalProtectedExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLInternalDefaultExceptionalPostconditionError) {
                throw new JMLInternalDefaultExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLInternalPrivateExceptionalPostconditionError) {
                throw new JMLInternalPrivateExceptionalPostconditionError(errorMsg, methodName, cause);
            } else if (JMLChecker.xPostconditionError instanceof JMLInternalExceptionalPostconditionError) {
                throw new JMLInternalExceptionalPostconditionError(errorMsg, methodName, cause);
            }
        }
    }

    public static void hasAnyThrownExceptionalPostconditionSignalsOnly() {
        if (JMLChecker.xPostconditionSignalsOnlyError != null) {
            String errorMsg = JMLChecker.xPostconditionSignalsOnlyError.toString();
            String methodName = ((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).methodName;
            Throwable cause = ((JMLExceptionalPostconditionError) JMLChecker.xPostconditionSignalsOnlyError).getRacCause();

            if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLExitPublicExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PUBLIC, methodName)) {
                    throw new JMLExitPublicExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLExitProtectedExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PROTECTED, methodName)) {
                    throw new JMLExitProtectedExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLExitDefaultExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(0L, methodName)) {
                    throw new JMLExitDefaultExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLExitPrivateExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PRIVATE, methodName)) {
                    throw new JMLExitPrivateExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLExitExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(-1, methodName)) {
                    throw new JMLExitExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            }

            if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLInternalPublicExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PUBLIC, methodName)) {
                    throw new JMLInternalPublicExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLInternalProtectedExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PROTECTED, methodName)) {
                    throw new JMLInternalProtectedExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLInternalDefaultExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(0L, methodName)) {
                    throw new JMLInternalDefaultExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLInternalPrivateExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(Constants.ACC_PRIVATE, methodName)) {
                    throw new JMLInternalPrivateExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            } else if (JMLChecker.xPostconditionSignalsOnlyError instanceof JMLInternalExceptionalPostconditionError) {
                if (JMLChecker.canThrowXPostconditionSignalsOnlyError(-1, methodName)) {
                    throw new JMLInternalExceptionalPostconditionError(errorMsg, methodName, cause);
                }
            }
        }
    }

    public static Throwable getXPostconditionError() {
        return JMLChecker.xPostconditionError;
    }

    public static void resetXPostconditionError() {
        JMLChecker.xPostconditionError = null;
    }

    private static StackTraceElement[] processAspectJMLStackTrace(StackTraceElement[] stackTrace) {
        final Vector newStackTraceList = new Vector();

        for (int i = 0; i < stackTrace.length; i++) {
            newStackTraceList.add(stackTrace[i]);
        }
        for (int i = 0; i < stackTrace.length; i++) {
            if (stackTrace[i].getClassName().contains("AspectJMLRac_")
                    || stackTrace[i].toString().contains("UtilPreconditionChecking")
                    || stackTrace[i].toString().contains("UtilNormalPostconditionChecking")
                    || stackTrace[i].toString().contains("UtilExceptionalPostconditionChecking")
                    || stackTrace[i].toString().contains("UtilInvariantChecking")
                    || stackTrace[i].toString().contains("UtilConstraintChecking")
                    || stackTrace[i].toString().contains("org.jmlspecs.ajmlrac.runtime.JMLChecker")
                    || stackTrace[i].toString().contains("_aroundBody")) {
                newStackTraceList.remove(stackTrace[i]);
            }
        }
        final StackTraceElement[] newStackTrace = new StackTraceElement[newStackTraceList.size()];

        for (int i = 0; i < newStackTraceList.size(); i++) {
            final StackTraceElement element = (StackTraceElement) newStackTraceList.get(i);
            newStackTrace[i] = element;
        }

        return newStackTrace;
    }

    public static void hideAjmlSpecificStackTrace(final Throwable exception) {
        if (exception == null) {
            throw new IllegalArgumentException("exception cannot be null at this point");
        }
        final StackTraceElement[] stackTrace = JMLChecker.processAspectJMLStackTrace(exception.getStackTrace());
        exception.setStackTrace(stackTrace);
    }

    public static String getThisJoinPointPartialMethSig(String longSig, String typeName) {
        String result = "";
        typeName = typeName.replace("$", ".");
        int index = longSig.indexOf(typeName);
        if (index != -1) {
            result = longSig.substring(longSig.indexOf(typeName));
        }
        return result;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /**
     * Runtime option indicating the assertion check level,
     * the kinds of assertions to be checked.
     * The default is <code>JMLOption.ALL</code>.
     * <p/>
     * <pre><jml>
     *  public invariant level == JMLOption.NONE ||
     *    level == JMLOption.PRECONDITIONS_ONLY ||
     *    level == JMLOption.ALL;
     * </jml></pre>
     */
    protected static /*@ spec_public @*/ int level = ALL;

    private static Stack checkedMethPreconditions = new Stack();
    private static Throwable nPostconditionError = null;
    private static Throwable xPostconditionError = null;
    private static Throwable xPostconditionSignalsOnlyError = null;
    private static Throwable invariantError = null;
    private static Throwable constraintError = null;
    private static Vector nPostconditionSat = new Vector();
    private static Vector xPostconditionSat = new Vector();
    private static Vector xPostconditionSignalsOnlySat = new Vector();
    private static Vector invariantSat = new Vector();
    private static Vector constraintSat = new Vector();
    public static boolean hasAnyJMLError = false;

    // Coverage methods

    /**
     * A map to hold information about coverage
     */
    static protected Hashtable coverage = new Hashtable();

    static public class CoverageCount {
        public String location;
        public int trueCount;
        public int falseCount;

        public CoverageCount(String loc) {
            location = loc;
        }

        public void incr(boolean v) {
            if (v) ++trueCount;
            else ++falseCount;
        }

    }

    static public void clearCoverage() {
        coverage = new Hashtable();
    }

    static public void addCoverage(String location, boolean value) {
        //java.lang.System.out.println("Adding " + location + " " + value);
        Object o = coverage.get(location);
        if (o == null) {
            o = new CoverageCount(location);
            coverage.put(location, o);
        }
        ((CoverageCount) o).incr(value);
    }

    static public void reportCoverage(java.io.PrintStream writer) {
        Enumeration i = coverage.elements();
        while (i.hasMoreElements()) {
            CoverageCount c = (CoverageCount) (i.nextElement());
            if (c.trueCount == 0 && c.falseCount == 0) {
                writer.println(c.location + ": The requires clause is NEVER executed");
            } else if (c.trueCount == 0 && c.falseCount > 0) {
                writer.println(c.location + ": The requires clause is always FALSE ("
                        + c.falseCount + " tests)");
            } else if (c.trueCount > 0 && c.falseCount == 0) {
                writer.println(c.location + ": The requires clause is always TRUE ("
                        + c.trueCount + " tests)");
            } else {
                //writer.println(c.location + " has " + c.trueCount + " true and " + c.falseCount + " false tests");
            }
        }
    }
}
