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
 * $Id: JmlGenericSpecCase.java,v 1.8 2006/12/20 06:16:01 perryjames Exp $
 */

package org.jmlspecs.checker;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.compiler.TokenReference;

/**
 * An AST node class for the JML <tt>generic-spec-case</tt>. The production
 * rule <tt>generic-spec-case</tt> is defined as follows.
 *
 * <pre>
 *  generic-spec-case :: = [ spec-var-decls ] spec-header [ generic-spec-body ]
 *    | [ spec-var-decls ] generic-spec-body
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.8 $
 */

public class JmlGenericSpecCase extends JmlGeneralSpecCase {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    //@ requires specHeader != null ==> specHeader.length > 0;
    //@ requires specVarDecls != null ==> specVarDecls.length > 0;
    //@ requires specHeader != null || genericSpecBody != null;
    public JmlGenericSpecCase(/*@ non_null */ TokenReference sourceRef,
			      /*@ nullable */ JmlSpecVarDecl[] specVarDecls,
			      /*@ nullable */ JmlRequiresClause[] specHeader,
			      /*@ nullable */ JmlGenericSpecBody genericSpecBody) {
	super(sourceRef, specVarDecls, specHeader, genericSpecBody);
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public /*@ non_null @*/ JmlGenericSpecBody genericSpecBody() {
	return (JmlGenericSpecBody) specBody;
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

    /** Returns the privacy of this node. By default, it returns that
     * of the method being checked. If the method has either
     * SPEC_PUBLIC or SPEC_PROTECTED modifier, then that modifier
     * takes a precedence over the JAVA access modifiers. */
    protected long privacy( /*@ non_null @*/ CFlowControlContextType context ) {
        //@ assert context.getCMethod() != null;
        long modifiers = context.getCMethod().modifiers();
        long privacy = modifiers & (ACC_SPEC_PUBLIC | ACC_SPEC_PROTECTED);
        if (privacy == 0) {
            privacy =  modifiers & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE);
        }
        return privacy;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept(/*@ non_null @*/ MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlGenericSpecCase(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
}
