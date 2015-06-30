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
 * $Id: Main.java,v 1.0 2009/02/20 16:48:06 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: VarGenerator.java,v 1.8 2002/10/27 20:49:11 leavens Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;


/**
 * A class for generating various uniques variable names for RAC.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public abstract class VarGenerator implements RacConstants {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /** Return a variable generator for classes */
    public static VarGenerator forClass() {
	return new VarGenForClass();
    }

    /** Return a variable generator for methods
     * 
     * @param forcls a variable generator for classes
     * 
     * <pre><jml>
     * requires forcls != null && (forcls instanceof VarGenForClass);
     * ensures \fresh(\result);
     * </jml></pre>
     */
    public static VarGenerator forMethod(VarGenerator forcls) {
	return new VarGenForMethod(forcls);
    }

    // ----------------------------------------------------------------------
    // NAME GENERATION METHODS
    // ----------------------------------------------------------------------
    
    /** Return a fresh variable name for storing the result of an old
     * expression or an old variable. The generated name is unique in
     * the class. The returned name is of the form: <code>VN_OLD_VAR +
     * n</code>, where <code>n</code> is a unique number.
     *
     * @see RacConstants#VN_OLD_VAR
     */
    public abstract String freshOldVar();

    /** Return a fresh variable name for storing the result of evaluating
     * a specification case of a precondtion. The returned name is unique
     * in the class. The returned name is of the form: <code>VN_PRE_VAR +
     * n</code>, where <code>n</code> is a unique number.
     *
     * @see RacConstants#VN_PRE_VAR
     */
    public abstract String freshPreVar();

    /** Return a fresh variable name for storing the result of evaluating
     * a specification case of a postcondition. The returned name is unique
     * in the method.
     * The returned name is of the form: <code>VN_POST_VAR +
     * n</code>, where <code>n</code> is a unique number.
     *
     * @see RacConstants#VN_POST_VAR
     */
    public abstract String freshPostVar();

    /** Return a fresh variable name for a stack for use as saving to
     * and restoring from pre-state values for potential recursive
     * method calls. The returned name is unique in the class.
     * The returned name is of the form: <code>VN_STACK_VAR +
     * n</code>, where <code>n</code> is a unique number.
     *
     * @see RacConstants#VN_STACK_VAR
     */
    public abstract String freshStackVar();

    /** Return a fresh variable name unique in the method. The
     * returned name is of the form: <code>VN_FREE_VAR + n</code>,
     * where <code>n</code> is a unique number.
     *
     * @see RacConstants#VN_FREE_VAR
     **/
    public abstract String freshVar();

    /** Return a fresh variable name for use in a catch clause. The
     * returned name is unique in the method scope and of
     * the form: <code>VN_CATCH_VAR + n</code>, where <code>n</code> is
     * a unique number.
     *
     * @see RacConstants#VN_FREE_VAR
     **/
    public abstract String freshCatchVar();

    // ----------------------------------------------------------------------
    // INNER CLASSES
    // ----------------------------------------------------------------------

    /** A variable generator for classes. */
    /*@ spec_public @*/ private static class VarGenForClass 
                            extends VarGenerator {
	private VarGenForClass() {
	    oldVarCnt = 0;
	    preVarCnt = 0;
            stackVarCnt = 0;
	}

	public String freshOldVar() {
	    return VN_OLD_VAR + (oldVarCnt++);
	}
	
	public String freshPreVar() {
	    return VN_PRE_VAR + (preVarCnt++);
	}

        /** Return a fresh variable name for a stack for use as saving to
         * and restoring from pre-state values for potential recursive
         * method calls. The returned name is unique in the class.
         */
        public String freshStackVar() {
            return VN_STACK_VAR + (stackVarCnt++);
        }

	public String freshPostVar() {
	    throw new UnsupportedOperationException();
	}

	public String freshCatchVar() {
	    throw new UnsupportedOperationException();
	}

	public String freshVar() {
	    throw new UnsupportedOperationException();
	}
	
	private int oldVarCnt;
	private int preVarCnt;
	private int stackVarCnt;
    }

    /** A variable generator for methods. */
    private static class VarGenForMethod extends VarGenerator {
	private VarGenForMethod(VarGenerator forClass) {
	    if (!(forClass instanceof VarGenForClass))
		throw new IllegalArgumentException();
	    this.forClass = forClass;
	    freeVarCnt = 0;
	    postVarCnt = 0;
	    oldVarCnt = 0;
	}

	public String freshOldVar() {
		//return forClass.freshOldVar();
		return VN_OLD_VAR + (oldVarCnt++); // by Henrique Rebelo
	}
	
	public String freshPreVar() {
	    return forClass.freshPreVar();
	}

        /** Return a fresh variable name for a stack for use as saving to
         * and restoring from pre-state values for potential recursive
         * method calls. The returned name is unique in the class.
         */
        public String freshStackVar() {
            return forClass.freshStackVar();
        }

	public String freshPostVar() {
	    return VN_POST_VAR + (postVarCnt++);
	}

	public String freshVar() {
	    return VN_FREE_VAR + (freeVarCnt++);
	}

	public String freshCatchVar() {
	    return VN_CATCH_VAR + (catchVarCnt++);
	}

	private VarGenerator forClass;
	private int postVarCnt;
	private int freeVarCnt;
	private int catchVarCnt;
	
	// henrique rebelo
	private int oldVarCnt; 
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
}
