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
 * $Id: InvariantMethodAdviceAsPostconditionMethod.java,v 1.0 2009/01/21 22:03:15 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.JMethodDeclarationType;

/**
 * A class for generating assertion check methods for class-level
 * assertions such as invariants and history constraints.
 * There are two types of class-level assertions:
 * <em>instance</em> (<em>non-static</em>) <em>assertions</em> and
 * <em>class</em> (<em>static</em>) <em>assertions</em>.
 * As thus, two types of assertion check methods are generated.
 * An instance assertion check method checks both the instance and class
 * assertions while a class assertion check method checks only the class
 * assertionss.
 * The generated assertion check methods inherit assertions of its superclass
 * interfaces by dynamically invoking the corresponding assertion methods.
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
public class InvariantMethodAdviceAsPostconditionMethod extends InvariantLikeMethod {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct a new <code>InvariantLikeMethod</code> object.
     *
     * @param isStatic the kind of assertion check method to generate;
     *                 <tt>true</tt> for static and <tt>false</tt> for
     *                 non-static (instance) assertion check method.
     * @param typeDecl the target type declaration whose assertion check
     *                 methods are to be generated.
     */
    public InvariantMethodAdviceAsPostconditionMethod(boolean isStatic, JmlTypeDeclaration typeDecl, VarGenerator varGen) {
        super(isStatic, typeDecl, varGen);
    }

    //	----------------------------------------------------------------------
    // GENERATION
    // ----------------------------------------------------------------------

    /**
     * Generate and return a type-level assertion check method such
     * as invariants and history constraints.  Append to the body
     * (<code>stmt</code>): (1) code to check the inherited assertions
     * if any, and (2) code to throw an appropriate exception to
     * notify an assertion violation.
     *
     * @param stmt code to evaluate the assertions; the result is supposed
     *             to be stored in the variable <code>VN_ASSERTION</code>.
     *             A <code>null</code> value means that no assertion is
     *             specified or the assertion is not executable.
     */
    public JMethodDeclarationType generate(RacNode stmt) {
        return null;
    }

    public JMethodDeclarationType generate() {
        StringBuffer code = buildAfterAdvice();
        return RacParser.parseMethod(code.toString(), null);
    }

    /**
     * Builds and returns the method header of the assertion check method as a
     * StringBuffer.
     */
    protected StringBuffer buildAfterAdvice() {
        // By Henrique Rebelo, Edited by: Anon
        String classQualifiedName = AspectUtil.replaceDollaSymbol(this.typeDecl.getCClass().getJavaName());
        final StringBuffer code = new StringBuffer();
        if ((this.hasInstInv) || (this.hasStatInv)) {
            code.append("\n");
            String adviceexecution = "";
            if (AspectUtil.getInstance().isTypeDeclAnAspect(this.typeDecl)) {
                adviceexecution = " || (adviceexecution())";
            }
            if (this.hasInstInv) {
                genJavadoc(code);
                genInstInv(classQualifiedName, code, adviceexecution, this.instInvPred);
            }
            if (this.hasStatInv) {
                genJavadoc(code);
                genStaticInv(classQualifiedName, code, adviceexecution, this.statInvPred);
            }
        }
        code.append("\n");
        return code;
    }

    private void genJavadoc(StringBuffer code) {
        if (this.javadoc != null) {
            code.append(this.javadoc);
        } else {
            code.append("/** Generated by AspectJML to check assertions. */");
        }
        code.append("\n");
    }

    private void genInstInv(String classQualifiedName, StringBuffer code, String adviceexecution, String invPred) {
        code.append("after (final ")
                .append(AspectUtil.replaceDollaSymbol(classQualifiedName))
                .append(" object$rac) :\n");
        code.append("   (execution(!static * ").append(classQualifiedName).append("+.*(..)) || \n");
        if (this.typeDecl.getCClass().isAbstract()) {
            code.append("     (execution(").append(classQualifiedName + "+.new(..))").append(" && !within(" + classQualifiedName + "))").append(adviceexecution).append(") && \n");
        } else {
            code.append("     execution(" + classQualifiedName + "+.new(..))").append(adviceexecution).append(") && \n");
        }
        code.append("   !execution(void ").append(classQualifiedName).append(".finalize() throws Throwable) && \n");
        if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4) {
            code.append("   !@annotation(JMLHelper) && \n");
        }
        code.append("   this(object$rac) {\n");
        {
            code.append(this.getQuantifierInnerClasses(invPred));
            code.append("        cute.Cute.Assert(").append(invPred).append(");\n");
        }
        code.append("  }\n");
    }

    private void genStaticInv(String classQualifiedName, StringBuffer code, String adviceexecution, String invPred) {
        code.append("after () :\n");
        // making static invariants inheritable to be checked on subtypes - hemr
        code.append("   (execution( * ").append(classQualifiedName).append("+.*(..)) || \n");
        if (this.typeDecl.getCClass().isAbstract()) {
            code.append("     (execution(").append(classQualifiedName).append("+.new(..)) && !within(").append(classQualifiedName).append(")) || \n");
        } else {
            code.append("     execution(").append(classQualifiedName).append("+.new(..)) || \n");
        }
        code.append("     staticinitialization(" + classQualifiedName + "+)").append(adviceexecution).append(")");
        if (!Main.aRacOptions.ajWeaver().startsWith("abc") && Float.parseFloat(Main.aRacOptions.source()) > 1.4) {
            code.append(" && \n");
            code.append("   !@annotation(JMLHelper)");
        }
        code.append("  {\n");
        {
            code.append(this.getQuantifierInnerClasses(invPred));
            code.append("        cute.Cute.Assert(").append(invPred).append(");\n");
        }
        code.append("  }\n");
    }

    protected /*@ pure @*/ boolean canInherit() {
        // TODO Auto-generated method stub
        return false;
    }
}
