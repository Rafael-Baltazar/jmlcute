/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, the type checker for the Java Modeling Language.
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
 * $Id: JmlMethodContext.java,v 1.13 2006/12/20 18:50:14 wdietl Exp $
 */

package org.jmlspecs.checker;

import java.util.Set;

import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodContext;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CSourceMethod;
import org.multijava.mjc.CThrowableInfo;
import org.multijava.mjc.CTypeVariable;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents the context for a method during checking
 * passes (checkInterface, checkInitializers, typecheck).
 * @see CContextType 
 */
public class JmlMethodContext extends JmlContext 
    implements CMethodContextType {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Create a context in which to check a method.
     * Clients should not call this but should instead call
     * <code>CClassContextType.createMethodContext</code>.
     *
     * <pre><jml>
     * requires (* \caller instanceof CContextType *);
     * </jml></pre>
     *
     * @param	parent		the parent context
     * @param	self		the corresponding method interface
     *
     * @see CClassContextType#createMethodContext(CMethod)
     */
    JmlMethodContext( CContextType parent, CMethod self ) {
	super(parent);
	delegee = new CMethodContext(parent, self);
    }

    protected JmlMethodContext(CContextType parent) {
	super(parent);
    }

    /**
     * Verifies that all checked exceptions are defined in the throw
     * list.
     *
     * @exception PositionedError if checks fail */
    public void verifyExceptions(TokenReference ref) throws PositionedError {
	((CMethodContext)delegee).verifyExceptions(ref);
    }

    // ----------------------------------------------------------------------
    // ACCESSORS (NEW CONTEXT)
    // ----------------------------------------------------------------------

    public CFlowControlContextType createFlowControlContext(int localVars,
							    TokenReference where)
    {
	return createFlowControlContext(localVars, false, where);
    }

    public CFlowControlContextType createFlowControlContext(
	int localVars, boolean isInExternalGF, TokenReference where) 
    {
	CFlowControlContextType retVal = new JmlFlowControlContext(this, localVars, isInExternalGF, where);
	retVal.adoptNullityInfo(this);
        return retVal;
    }

    
    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Returns the signature of the method declaration in which this
     * context is enclosed, or null if this context is not enclosed in
     * a method declaration.
     */
    //@ pure
    public CMethod getCMethod() {
	CMethod meth = delegee.getCMethod();
	if (! (meth instanceof JmlSourceMethod) ) {
	    // !FIXME! This should NOT be necessary.  This is just 
	    // a work around for those few very rare cases (bug?) when
	    // the method in this context is not a JmlSourceMethod object.
	    // It's only happened for constructors or initializers (and 
	    // for some reason only in junit tests).
	    meth = new JmlSourceMethod((CSourceMethod) meth);
	}
	return meth;
    }

    /**
     * Returns the nearest surrounding context of type CMethodContext.  */
    public CMethodContextType getMethodContext() {
	return this;
    }

    public CTypeVariable lookupTypeVariable(String ident) throws UnpositionedError {
        CTypeVariable tv = getCMethod().lookupTypeVariable(ident);
        if (tv != null) { 
            return tv;
        } else { 
            if (isStatic()) {
                return null;
            } else {
                return getClassContext().lookupTypeVariable(ident);
            }
        }
    }

    /**
     * Indicates whether this context is enclosed in an instance or
     * static initializer.  */
    public boolean isInInitializer() {
	return delegee.isInInitializer();
    }

    /**
     * Indicates whether this context is enclosed in a constructor.  */
    public boolean isInConstructor() {
	return delegee.isInConstructor();
    }

    /**
     * Indicates whether this context is "static".
     *
     * @return true iff this context is enclosed in a context for a
     * static initializer or static method.  */
    public boolean isStatic() {
	return delegee.isStatic();
    }

    /**
     * Indicates whether this context is "pure".  By WMD.
     *
     * @return true iff this context is enclosed in a pure method.
     */
    public boolean isPure() {
	return delegee.isPure();
    }

    // ----------------------------------------------------------------------
    // THROWABLES
    // ----------------------------------------------------------------------

    /**
     * @param	throwable	the type of the new throwable
     */
    public void addThrowable(CThrowableInfo throwable) {
	((CMethodContext)delegee).addThrowable(throwable);
    }

    /**
     * @return the list of exception that may be thrown
     */
    public Set throwables() {
	return ((CMethodContext)delegee).throwables();
    }
}
