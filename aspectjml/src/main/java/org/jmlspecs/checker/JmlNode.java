/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML Project.
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
 * $Id: JmlNode.java,v 1.12 2007/04/18 23:04:37 leavens Exp $
 */

package org.jmlspecs.checker;
import org.multijava.util.compiler.*;
import org.multijava.mjc.*;

/**
 * This is the superclass of most JML AST nodes.  However, some JML
 * AST nodes must directly subclass mjc AST nodes.  */
public abstract class JmlNode extends JPhylum implements Constants { 

    public JmlNode( /*@ non_null */ TokenReference where ) {
	super( where );
    }

    /**
     * Throws an UnsupportedOperationException since an MjcVisitor
     * cannot be used to visit a JML AST.  */
    public void accept( /*@non_null@*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor) ((JmlVisitor)p).visitJmlNode(this);
	else throw new UnsupportedOperationException( MJCVISIT_MESSAGE );
    }

    /** 
     * Enters a new JML specification scope if the argument contains 
     * "model", "ghost" or "extract" modifiers.
     *
     * @see JmlContext#enterSpecScope( )
     * @see JStatementWrapper#enterSpecScope(int)
     */
    public static void enterSpecScope(long modifiers) {
	if (hasFlag(modifiers, ACC_MODEL) || hasFlag(modifiers, ACC_GHOST) 
	    || hasFlag(modifiers, ACC_EXTRACT)) {
	    JmlContext.enterSpecScope();
	}
    }

    /** 
     * Enters a new JML specification scope.
     *
     * @see JmlContext#enterSpecScope()
     * @see JStatementWrapper#enterSpecScope()
     */
    public static void enterSpecScope() {
	    JmlContext.enterSpecScope();
    }

    /** 
     * Exits the current JML specification scope if the argument contains 
     * "model", "ghost" or "extract" modifiers.
     *
     * @see JmlContext#exitSpecScope()
     * @see JStatementWrapper#exitSpecScope(int)
     */
    public static void exitSpecScope(long modifiers) {
	if (hasFlag(modifiers, ACC_MODEL) || hasFlag(modifiers, ACC_GHOST)
	    || hasFlag(modifiers, ACC_EXTRACT)) {
	    JmlContext.exitSpecScope();
	}
    }

    /** 
     * Exits the current JML specification scope.
     *
     * @see JmlContext#exitSpecScope()
     * @see JStatementWrapper#exitSpecScope()
     */
    public static void exitSpecScope() {
	JmlContext.exitSpecScope();
    }

    //---------------------------------------------------------------------
    // HELPER METHODS
    //---------------------------------------------------------------------

    /** Returns the access (privacy) modifier of the given modifiers,
     * <code>modifiers</code>. If the modifiers has either SPEC_PUBLIC
     * or SPEC_PROTECTED, then that access modifier takes a precedence
     * over the JAVA access modifiers.
     */
    protected static /*@ pure @*/ long privacy(long modifiers) {
        // can have multiple access modifiers, so explicitly
        // check from the most visible to the least visible ones.
        if (hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_PUBLIC))
            return ACC_PUBLIC;
        else if (hasFlag(modifiers, ACC_SPEC_PROTECTED | ACC_PROTECTED))
            return ACC_PROTECTED;
        else if (hasFlag(modifiers, ACC_PRIVATE))
            return ACC_PRIVATE;
        else
            return 0L; // package
    }

    /** Return a string representation of the given visibility; the 
	argument may be the complete set of modifiers; note that 
	"package" is returned if no visibility level is specified.
     * <pre><jml>
	ensures \result != null;
     * </jml></pre> 
     */
    public static /*@ non_null @*/ String privacyString(long privacy) {
	if (hasFlag(privacy,ACC_PUBLIC|ACC_SPEC_PUBLIC))
		return "public";
	else if (hasFlag(privacy,ACC_PROTECTED|ACC_SPEC_PROTECTED))
		return "protected";
	else if (hasFlag(privacy,ACC_PRIVATE))
		return "private";
	else 
		return "package";
/* This is the old code; modified to allow values of 'modifiers' to be used
        switch (privacy) {
        case ACC_PUBLIC:
        case ACC_SPEC_PUBLIC:
            return "public";
        case ACC_PROTECTED:
        case ACC_SPEC_PROTECTED:
            return "protected";
        case 0: 
            return "package";
        case ACC_PRIVATE:
            return "private";
        default:
            //@ unreachable;
        }
        return "";
*/
    }

    //---------------------------------------------------------------------
    // INNER CLASSES
    //---------------------------------------------------------------------

    /** A class for dummy initializer declarations. A dummy initializer
     * declaration is used to typecheck JML declarations such as
     * invariant, constraint, depends, and represents clauses.
     */
    static class DummyInitializerDeclaration extends JInitializerDeclaration {
        DummyInitializerDeclaration(TokenReference where, boolean isStatic) {
            super(where, null, isStatic, true);
        }

        /** Returns a context for this dummay initializer declaration.
         * It is overriden here to written a method contxt (not initializer
         * context) not to check definite assignment of referenced fields.
         */
        public CMethodContextType createSelfContext(/*@non_null@*/ CClassContextType parent) {
            return parent.createMethodContext(getMethod());
        }
    }

    //---------------------------------------------------------------------
    // DATA MEMBERS
    //---------------------------------------------------------------------

    public static final String MJCVISIT_MESSAGE =
	"cannot visit a JML AST with a MjcVisitor";
}

