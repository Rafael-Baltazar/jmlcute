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
 * $Id: PreconditionMethodAdvice.java,v 1.0 2009/01/15 05:11:33 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: PreconditionMethod.java,v 1.13 2007/07/19 10:51:36 f_rioux Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.JMethodDeclarationType;

/**
 * A class for generating a precondition check method as an AspecJ advice.
 * The precondition checking code is automatic wrapped with code that checks
 * the inherited preconditions if any, and throws an appropriate exception to
 * signal a violation if the precondition is violated.
 * <p/>
 * <p>
 * The class implements a variant of the <em>Template Pattern</em>
 * [GoF95], prescribed in the class {@link AssertionMethod}.
 * </p>
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 * @see AssertionMethod
 */

public class PreconditionMethodAdvice extends PreOrPostconditionMethod {

    /**
     * Construct a new <tt>PreconditionMethodITD</tt> object.
     *
     * @param mdecl        method for which the precondition method is generated
     * @param hasAssertion <code>true</code> if <code>mdecl</code> has
     *                     a precondition specification
     */
    public PreconditionMethodAdvice(JmlTypeDeclaration typeDecl,
                                    JmlMethodDeclaration mdecl,
                                    boolean hasAssertion,
                                    String saveMethod) {
        super(typeDecl, mdecl, saveMethod);
        this.hasAssertion = hasAssertion;
        this.prefix = MN_CHECK_PRE;
        this.methodName = prefix + methodName(mdecl) + "$" + typeDecl.ident();
        this.exceptionToThrow = "JMLEntryPreconditionError";
        boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);
        this.javadoc = new StringBuilder("/**\n * Generated by AspectJML to check the precondition of ")
                .append(isMethodCrosscutSpecChecking ? "members intercepted by " : "method ")
                .append(mdecl.ident()).append(" pointcut.\n */").toString();
    }

    // ----------------------------------------------------------------------
    // GENERATION
    // ----------------------------------------------------------------------

    public JMethodDeclarationType generate(RacNode stmt) {
        throw new UnsupportedOperationException();
    }

    public JMethodDeclarationType generate(RacNode stmt, String pred, String instrumentationType, long visibility) {
        StringBuffer code = new StringBuffer("");
        if (this.hasAssertion) {
            pred = AspectUtil.changeThisOrSuperRefToAdviceRef(pred, typeDecl);
            boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);
            StringBuffer codeTmp = this.buildAdviceHeader("PreconditionAssertionMethod", instrumentationType, visibility, isMethodCrosscutSpecChecking);
            code.append(codeTmp.toString());
            code.append("  {\n");
            code.append("    cute.Cute.Assert(").append(pred).append(");\n");
            code.append("  }\n");
        }
        return RacParser.parseMethod(code.toString(), stmt);
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
    private boolean hasAssertion;
}
