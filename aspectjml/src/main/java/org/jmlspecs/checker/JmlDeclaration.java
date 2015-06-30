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
 * $Id: JmlDeclaration.java,v 1.15 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;

import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.mjc.*;

/**
 * This abstract class is the superclass of all jml-declaration AST
 * nodes, (i.e., invariants, history constraints, depends
 * declarations, and represents declarations)
 */
public abstract class JmlDeclaration extends JmlNode 
    implements Cloneable
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    /**
     * Creates a new <code>JmlDeclaration</code> instance.
     *
     * @param where a <code>TokenReference</code> value
     * @param modifiers an <code>int</code> value
     * @param redundantly indicates whether this is a redundant annotation
     */
    public JmlDeclaration( /*@ non_null */ TokenReference where, long modifiers, 
			   boolean redundantly ) {
	super( where );
	this.modifiers = modifiers;
	this.redundantly = redundantly;
    }

    /**
     * All subclasses must be clonable.  */
    public /*@non_null@*/ Object clone() {
	try {
	    return super.clone();
	} catch ( CloneNotSupportedException e ) {
	    // Superclass should be clonable. It declares
	    // CloneNotSupportedException so that subclasses can
	    // choose to not be clonable.
	    throw new IllegalStateException("unreachable code reached!");
	}
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    /**
     * Returns the bit-mask representing the modifiers of this
     * declaration.
     *
     * @return an <code>int</code> value formed by bit-wise ORing of 
     * constants from Constants.
     *
     * @see Constants
     */
    public long modifiers() {
	return modifiers;	
    }

    /** Returns the privacy of this declaration. If the modifiers has
     * either SPEC_PUBLIC or SPEC_PROTECTED, then that access modifier
     * takes a precedence over the JAVA access modifiers.
     */
    protected long privacy() {
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

    /**
     * Returns true if this JML declaration is a static declaration.
     */
    public boolean isStatic() {
	return hasFlag(modifiers, ACC_STATIC);
    }

    /**
     * Indicates whether this is declared to be a redundant declaration.
     */
    public boolean isRedundantly() {
	return redundantly;
    }

    //---------------------------------------------------------------------
    // Visitor
    //---------------------------------------------------------------------

    public void accept(/*@ non_null @*/ MjcVisitor m) {
        ((JmlVisitor)m).visitJmlDeclaration(this);
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

   /**
     * Typechecks this invariant clause in the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this type declaration appears
     * @exception PositionedError if any checks fail */
    public abstract void typecheck(/*@ non_null @*/ CContextType context ) 
	throws PositionedError;

    /**
     * Create a JmlExpressionContext object as a child of the given
     * (CClassContextType) context that can be used to typecheck
     * this JML declaration.
     *
     * @param context the pararent context
     */
    protected /*@ non_null @*/ JmlExpressionContext createContext(/*@ non_null @*/ CContextType context ) 
    {
        CFlowControlContextType fctx = createContextHelper(context);
        return JmlExpressionContext.createIntracondition(fctx);
    }

    /** Returns a flow control context object that can be used to create
     * an expression context objec to typecheck this JML declaration.
     */
    protected /*@ non_null @*/ CFlowControlContextType createContextHelper(
            /*@ non_null @*/ CContextType context) {
        
        // dummy declaration to host typechecking of this JML declaration
        JMethodDeclaration init = new DummyInitializerDeclaration(
            getTokenReference(), 
            hasFlag(modifiers, ACC_STATIC));

        // generate signature (CMethod) object
        try {
            init.checkInterface( context ); 
        } catch (PositionedError e) {
	    throw new RuntimeException("Unreachable! " +  e.getMessage());
	}

        CMethodContextType mctx = 
            init.createSelfContext((CClassContextType)context);
        return mctx.createFlowControlContext(0, getTokenReference());
    }

    /**
     * Checks the modifiers of this JML declaration. Allowed modifiers are
     * PUBLIC, PROTECTED, PRIVATE, STATIC, and INSTANCE. At most one of
     * privacy modifiers is allowed and similarly at most one of STATIC
     * and INSTANCE is allowed.
     */
    protected void checkModifiers(/*@ non_null @*/CContextType context)
        throws PositionedError {

        // only public, protected, private, static, and instance
        check(context,
              !hasOtherFlags(modifiers,
                             ACC_PUBLIC + ACC_PROTECTED + ACC_PRIVATE +
                             ACC_STATIC + ACC_INSTANCE),
              JmlMessages.JML_DECLARATION_FLAGS);

        // only one of static and instance
        check(context,
              !(hasFlag(modifiers, ACC_STATIC) && 
                hasFlag(modifiers, ACC_INSTANCE)),
              JmlMessages.JML_FLAGS_STATIC_AND_INSTANCE);                      

        // only one of public, protected, and private
        class ModifierAccumulator {
            void check(long flag) {
                if (hasFlag(modifiers, flag)) {
                    count++;
                }
            }
            boolean hasMultiple() {
                return count > 1;
            }
            private int count = 0;
        }
        ModifierAccumulator acc = new ModifierAccumulator();
        acc.check(ACC_PUBLIC);
        acc.check(ACC_PROTECTED);
        acc.check(ACC_PRIVATE);
        check(context, !acc.hasMultiple(), 
              JmlMessages.JML_FLAGS_MULTIPLE_PRIVACY);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * The bit-mask representing the modifiers of this declaration.
     * */
    protected long modifiers;

    /**
     * Indicates whether this is a redundant annotation.  */
    protected final boolean redundantly;
}
