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
 * $Id: PreOrPostconditionMethod.java,v 1.0 2008/0715/19 9:32:03 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: PreOrPostconditionMethod.java,v 1.13 2005/12/09 19:46:03 f_rioux Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jmlspecs.checker.Constants;
import org.jmlspecs.checker.JmlAbstractVisitor;
import org.jmlspecs.checker.JmlConstructorDeclaration;
import org.jmlspecs.checker.JmlFormalParameter;
import org.jmlspecs.checker.JmlMessages;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JStatement;
import org.multijava.util.compiler.TokenReference;

import com.thoughtworks.qdox.model.Annotation;
import com.thoughtworks.qdox.model.JavaMethod;

/**
 * An abstract class for generating <em>precondition</em> or
 * <em>postconditin checking method as an AspectJ advice</em> for the given methods.
 * The generated assertion method automatic inherit its superclass's
 * assertions.
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

public abstract class PreOrPostconditionMethod extends AssertionMethod {
    /**
     * Construct a new <code>PreOrPostconditionMethod</code> object.
     */
    protected PreOrPostconditionMethod(JmlTypeDeclaration typeDecl,
                                       JmlMethodDeclaration mdecl,
                                       String stackMethod) {
        this.typeDecl = typeDecl;
        this.methodDecl = mdecl;
        name = mdecl.ident();
        this.methodIdentification = "\"" + name + "\"";
        this.parameters = mdecl.parameters();

        boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);
        if (isMethodCrosscutSpecChecking) {
            JavaMethod crosscutSpecCheckingMethod = AspectUtil.getInstance().getJavaMethCrosscutSpecChecking(this.methodDecl);
            Annotation pcAnno = null;
            // getting pointcut's value
            for (int i = 0; i < crosscutSpecCheckingMethod.getAnnotations().length; i++) {
                Annotation currentAnno = crosscutSpecCheckingMethod.getAnnotations()[i];
                if ((currentAnno.toString().startsWith("@org.aspectj.lang.annotation"))) {
                    pcAnno = currentAnno;
                }
            }
            String xcsPointcut = pcAnno.getProperty("value").getParameterValue().toString().
                    replaceAll("\"(\\s)*\\+(\\s)*\"", "").replace("\"", "");
            Pattern staticPattern = Pattern.compile("\\bstatic\\b");
            Matcher staticMatcher = staticPattern.matcher(xcsPointcut.replaceAll("!(\\s)*static", ""));

            if (staticMatcher.find()) {
                this.isStatic = true;
            }
        } else {
            this.isStatic = this.methodDecl.isStatic();
        }
        this.exceptionToThrow = "JMLAssertionError";
    }

    // ----------------------------------------------------------------------
    // GENERATION
    // ----------------------------------------------------------------------

    /**
     * Indicates whether the generated assertion method should try to
     * dynamically inherit the corresponding assertion method of the
     * superclass or interfaces.  Method specifications are inherited
     * only for instance (non-static) methods; i.e., class (static)
     * method specifications are not inherited by subclasses. Also,
     * method specifications for constructors are not inherited by
     * subclasses.  Dynamic inheritance is costly, so attempted only
     * if the method has a superclass (or interfaces) and is
     * overriding any of its superclass methods.
     * <p/>
     * <pre><jml>
     * also
     * protected normal_behavior
     *   ensures \result == !isStatic
     *     && !(methodDecl instanceof JmlConstructorDeclaration)
     *     && methodDecl.isOverriding();
     * </jml></pre>
     */
    protected /*@ pure @*/ boolean canInherit() {
        return
                // don't try to inherit from Object
                (hasExplicitSuperClass() || typeDecl.interfaces().length > 0)
                        && !isStatic
                        && !(methodDecl instanceof JmlConstructorDeclaration)
                        && methodDecl.isOverriding();
    }

    /**
     * Returns the name of assertion check method to be generated for
     * the given method declaration. For constructors, the result is
     * MN_INIT; for non-constructors, the result is the same as the name
     * of the given method declaration.
     */
    protected static String methodName(JmlMethodDeclaration mdecl) {
        return (mdecl instanceof JmlConstructorDeclaration) ?
                MN_INIT : mdecl.ident();
    }

    protected StringBuffer buildAdviceHeader(String assertionMethType, String instrumentationType, long visibility,
                                             boolean isMethodCrosscutSpecChecking) {
        final StringBuffer code = new StringBuffer("");
        String codeStr = "";
        String classQualifiedName = this.methodDecl.getMethod().owner().getJavaName();
        String methodQualifiedName;
        String methodQualifiedNameJP = this.methodDecl.getMethod().getJavaName();

        if (this.methodDecl.isConstructor()) {
            if (this.methodDecl.getMethod().owner().isInnerClass()) {
                methodQualifiedName = this.methodDecl.stringRepresentation();
                methodQualifiedName = methodQualifiedName.replace(this.typeDecl.getCClass().getJavaName() + ", ", "");
                methodQualifiedName = methodQualifiedName.replace(this.methodDecl.getMethod().owner().ident(),
                        this.methodDecl.getMethod().owner().ident() + ".new").replaceAll("<(.)*>", ""); // removing the Java 5 Diamond --- [[[hemr]]]
            } else {
                methodQualifiedName = this.methodDecl.stringRepresentation().replace(this.methodDecl.getMethod().owner().ident(),
                        this.methodDecl.getMethod().owner().ident() + ".new").replaceAll("<(.)*>", ""); // removing the Java 5 Diamond --- [[[hemr]]]
            }
        } else {
            if (this.methodDecl.isStatic()) {
                methodQualifiedName = this.methodDecl.getMethod().getJavaName();
            } else {
                if (instrumentationType.equals("clientAwareChecking") || instrumentationType.equals("executionSite")) {
                    methodQualifiedName = this.methodDecl.getMethod().getJavaName();
                } else {
                    methodQualifiedName = this.methodDecl.getMethod().getJavaName().replace(classQualifiedName + ".", "");
                }
            }
        }

        // handling crosscutting contract specifications --- [[[hemr]]]
        String xcsPointcut = "";

        boolean isXCSPointcutStatic = false;

        if (isMethodCrosscutSpecChecking) {
            JavaMethod crosscutSpecCheckingMethod = AspectUtil.getInstance().getJavaMethCrosscutSpecChecking(this.methodDecl);
            String xcsParentClassName = "";
            String xcsParentClassFullyQualifiedName = "";

            // checking if the crosscutSpecCheckingMethod is for an interface
            if (AspectUtil.getInstance().isCrosscuttingContractSpecificationForInterface(crosscutSpecCheckingMethod)) {
                classQualifiedName = AspectUtil.replaceDollaSymbol(crosscutSpecCheckingMethod.getParentClass().getParentClass().getFullyQualifiedName());
                xcsParentClassName = crosscutSpecCheckingMethod.getParentClass().getParentClass().getName();
                xcsParentClassFullyQualifiedName = crosscutSpecCheckingMethod.getParentClass().getParentClass().getFullyQualifiedName().replace("$", ".");
            } else {
                classQualifiedName = AspectUtil.replaceDollaSymbol(crosscutSpecCheckingMethod.getParentClass().getFullyQualifiedName());
                xcsParentClassName = crosscutSpecCheckingMethod.getParentClass().getName();
                xcsParentClassFullyQualifiedName = crosscutSpecCheckingMethod.getParentClass().getFullyQualifiedName().replace("$", ".");
                ;
            }

            Annotation pcAnno = null;
            boolean flexibleXCS = false;
            // getting pointcut's value
            for (int i = 0; i < crosscutSpecCheckingMethod.getAnnotations().length; i++) {
                Annotation currentAnno = crosscutSpecCheckingMethod.getAnnotations()[i];
                if ((currentAnno.toString().startsWith("@org.aspectj.lang.annotation.Pointcut"))) {
                    pcAnno = currentAnno;
                }
                if ((currentAnno.toString().startsWith("@org.jmlspecs.lang.annotation.FlexibleXCS")) ||
                        (currentAnno.toString().startsWith("@org.jmlspecs.lang.annotation.GlobalXCS"))) {
                    flexibleXCS = true;
                    isXCSPointcutStatic = true;
                }
            }
            String xcsPCTmp = pcAnno.getProperty("value").getParameterValue().toString().
                    replaceAll("\"(\\s)*\\+(\\s)*\"", "").replace("\"", "");

            xcsPCTmp = processingXCSPointcut(xcsParentClassName,
                    xcsParentClassFullyQualifiedName, pcAnno, xcsPCTmp, flexibleXCS);

            if (!flexibleXCS) {
                // processing reusable pointcuts --- [[[hemr]]]
                List javaMethXCS = AspectUtil.getInstance().getCrosscutSpecMeths();
                for (Iterator iterator = javaMethXCS.iterator(); iterator
                        .hasNext(); ) {
                    JavaMethod currentJavaMethod = (JavaMethod) iterator.next();

                    Pattern thisPattern = Pattern.compile("\\.\\b" + Pattern.quote(currentJavaMethod.getName()) + "\\b");
                    Matcher thisMatcher = thisPattern.matcher(xcsPCTmp);
                    if (!thisMatcher.find()) {
                        Pattern thisPatternAux = Pattern.compile("\\b" + Pattern.quote(currentJavaMethod.getName()) + "\\b");
                        Matcher thisMatcherAux = thisPatternAux.matcher(xcsPCTmp);
                        if (thisMatcherAux.find()) {
                            //testing if it is local
                            if (currentJavaMethod.getParentClass().getFullyQualifiedName().equals(typeDecl.getCClass().getJavaName())) {
                                xcsPCTmp = xcsPCTmp.replace(thisMatcherAux.group(), typeDecl.getCClass().getJavaName() + "." + thisMatcherAux.group());
                                // verifying if the reused pointcut is static
                                for (int i = 0; i < currentJavaMethod.getAnnotations().length; i++) {
                                    Annotation currentAnno = currentJavaMethod.getAnnotations()[i];
                                    if ((currentAnno.toString().startsWith("@org.aspectj.lang.annotation"))) {
                                        pcAnno = currentAnno;
                                    }
                                }
                                String xcsPCTmp2 = pcAnno.getProperty("value").getParameterValue().toString().
                                        replaceAll("\"(\\s)*\\+(\\s)*\"", "").replace("\"", "");

                                Pattern staticPattern = Pattern.compile("\\bstatic\\b");
                                Matcher staticMatcher = staticPattern.matcher(xcsPCTmp2.replaceAll("!(\\s)*static\\b", ""));
                                if (staticMatcher.find()) {
                                    isXCSPointcutStatic = true;
                                }
                            } else {
                                ArrayList allOverriddenMethodsFromSuperClasses = new ArrayList();
                                this.typeDecl.getCClass().getAllMethods(allOverriddenMethodsFromSuperClasses);
                                for (Iterator iterator2 = allOverriddenMethodsFromSuperClasses
                                        .iterator(); iterator2.hasNext(); ) {
                                    CMethod currentInheritedMeth = (CMethod) iterator2.next();
                                    if (currentJavaMethod.getParentClass().getFullyQualifiedName().equals(currentInheritedMeth.owner().getJavaName())) {
                                        xcsPCTmp = xcsPCTmp.replace(thisMatcherAux.group(), currentInheritedMeth.owner().getJavaName() + "." + thisMatcherAux.group());
                                        // verifying if the reused pointcut is static
                                        for (int i = 0; i < currentJavaMethod.getAnnotations().length; i++) {
                                            Annotation currentAnno = currentJavaMethod.getAnnotations()[i];
                                            if ((currentAnno.toString().startsWith("@org.aspectj.lang.annotation"))) {
                                                pcAnno = currentAnno;
                                            }
                                        }
                                        String xcsPCTmp2 = pcAnno.getProperty("value").getParameterValue().toString().
                                                replaceAll("\"(\\s)*\\+(\\s)*\"", "").replace("\"", "");

                                        Pattern staticPattern = Pattern.compile("\\bstatic\\b");
                                        Matcher staticMatcher = staticPattern.matcher(xcsPCTmp2.replaceAll("!(\\s)*static\\b", ""));
                                        if (staticMatcher.find()) {
                                            isXCSPointcutStatic = true;
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }

                // avoiding property-based type pattern in XCS --- [[[hemr]]]
                Pattern namePropertyBasedTypePattern = Pattern.compile("\\*(\\.)?(\\.)?\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b" + "(\\s)*(\\+)?(\\s)*\\.");
                Matcher namePropertyBasedTypePatternMatcher = namePropertyBasedTypePattern.matcher(xcsPCTmp);
                if (namePropertyBasedTypePatternMatcher.find()) {
                    JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                            JmlMessages.PROPERTY_BASED_POINTCUT_NOT_ALLOWED, this.methodDecl.ident(), xcsParentClassFullyQualifiedName);
                    System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                }

                namePropertyBasedTypePattern = Pattern.compile("\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b" + "(\\*)?(\\.)?(\\.)?\\*(\\s)*(\\+)?(\\s)*\\.");
                namePropertyBasedTypePatternMatcher = namePropertyBasedTypePattern.matcher(xcsPCTmp);
                if (namePropertyBasedTypePatternMatcher.find()) {
                    JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                            JmlMessages.PROPERTY_BASED_POINTCUT_NOT_ALLOWED, this.methodDecl.ident(), xcsParentClassFullyQualifiedName);
                    System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                }

                namePropertyBasedTypePattern = Pattern.compile("\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b" + "(\\*)?(\\.\\.)?(\\*(\\w)*(\\*)?)*?(\\s)*\\(");
                namePropertyBasedTypePatternMatcher = namePropertyBasedTypePattern.matcher(xcsPCTmp);
                if (namePropertyBasedTypePatternMatcher.find()) {
                    JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                            JmlMessages.PROPERTY_BASED_POINTCUT_NOT_ALLOWED, this.methodDecl.ident(), xcsParentClassFullyQualifiedName);
                    System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                }

                // handling static join points --- [[[hemr]]]
                // #1 verifying if all static pointcuts if any are defined for all pointcuts
                Pattern staticPattern = Pattern.compile("\\bstatic\\b");
                Matcher staticMatcher = staticPattern.matcher(xcsPCTmp.replaceAll("!(\\s)*static\\b", ""));
                int execCallCount = 0;
                if (staticMatcher.find()) {
                    int staticCount = 1;
                    isXCSPointcutStatic = true;
                    while (staticMatcher.find()) {
                        staticCount++;
                    }

                    Pattern execCallPattern = Pattern.compile("(execution(\\s)*\\()|(call(\\s)*\\()");
                    Matcher execCallMatcher = execCallPattern.matcher(xcsPCTmp);
                    while (execCallMatcher.find()) {
                        execCallCount++;
                    }
                    if (!(staticCount == execCallCount)) {
                        JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                                JmlMessages.INVALID_STATIC_AND_INSTANCE_POINTCUT_TOGETHER, this.methodDecl.ident());
                        System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                    }
                } else {
                    execCallCount = -1;
                }

                // #2 if they are valid static pointcuts, we must ensure that they mention its enclosing type
                if (isXCSPointcutStatic) {
                    Pattern nameTypePattern = Pattern.compile("\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b" + "(\\s)*(\\+)?(\\s)*\\.((\\*)?(\\w)*(\\*)?)*?(\\s)*\\(");
                    Matcher nameTypePatternMatcher = nameTypePattern.matcher(xcsPCTmp);
                    int nameTypePatternCount = 0;
                    while (nameTypePatternMatcher.find()) {
                        nameTypePatternCount++;
                    }
                    if (execCallCount != -1) {
                        if (!(nameTypePatternCount == execCallCount)) {
                            JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                                    JmlMessages.INVALID_STATIC_POINTCUT, this.methodDecl.ident(), xcsParentClassFullyQualifiedName);
                            System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                        }
                    }

                    // #3 static pointcuts cannot refer to instance members
                    if (AspectUtil.getInstance().hasThisRef) {
                        JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), pcAnno.getLineNumber()),
                                JmlMessages.NO_THIS_REF_IN_STATIC_POINTCUT, this.methodDecl.ident());
                        System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
                    }

                    // util for code generation in XCS mode --- [[[hemr]]]
                    AspectUtil.getInstance().isStaticPC = true;
                }
            }

            // getting the processed PC
            xcsPointcut = xcsPCTmp;
//        	System.out.println("xcsPointcut = "+xcsPointcut);

            // appending pointcuts for crossrefs generation --- [[[hemr]]]
            if (Main.aRacOptions.crossrefs() != null) {
                if (assertionMethType.equals("XPAssertionMethodWithAfterThrowingAdvice") || assertionMethType.equals("NPAndXPAssertionMethodsWithAroundAdvice")) {
                    StringBuffer util = new StringBuffer("");
                    if (!isXCSPointcutStatic) {
                        util.append(" && target(" + xcsParentClassFullyQualifiedName + ")");
                    }
                    if (Main.aRacOptions.clientAwareChecking()) {
                        String packageQualifiedName = this.methodDecl.getMethod().owner().packageName().replace("/", ".");
                        if (visibility == ACC_PROTECTED) {
                            util.append(" && ");
                            util.append("(within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                        } else if (visibility == 0L) {//package
                            util.append(" && ");
                            util.append("within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                        } else if (visibility == ACC_PRIVATE) {
                            util.append(" && ");
                            util.append("within(" + classQualifiedName + ")"); // n, p, thisJoinPoint, j, i
                        }
                    }
                    StringBuffer crossRefAdvice = new StringBuffer("");
                    JavaMethod jm = AspectUtil.getInstance().getCorrespondingJavaMethodThroughJMLMethod(this.methodDecl.getMethod().owner().getJavaName(), this.methodDecl);
                    String methParamTypes = "";
                    String methParamTypeNames = "";
                    String methParamNames = "";
                    if (jm != null) {
                        methParamTypes = AspectUtil.generateMethodParameters(jm.getParameters(), false).toString();
                        methParamTypeNames = AspectUtil.generateMethodParameters(jm.getParameters(), true).toString();
                        methParamNames = AspectUtil.generateMethodParametersOnlyParamNames(jm.getParameters()).toString();
                    } else {
                        methParamTypes = AspectUtil.generateMethodParameters(parameters, false).toString();
                        methParamTypeNames = AspectUtil.generateMethodParameters(this.parameters, true).toString();
                        methParamNames = AspectUtil.generateMethodParametersOnlyParamNames(this.parameters).toString();
                    }

                    crossRefAdvice.append("  /** Generated by AspectJML to enable the crossreferences for the XCS pointcut {@link " +
                            crosscutSpecCheckingMethod.getParentClass().getFullyQualifiedName().replace("$", ".") + "#" + this.methodDecl.ident() +
                            methParamTypes + "} */\n");
                    String pcParameters = methParamTypeNames;
                    // handling the thisJoinPoint declaration
                    pcParameters = pcParameters.replace("org.aspectj.lang.JoinPoint thisJoinPoint, ", "").replace(", org.aspectj.lang.JoinPoint thisJoinPoint", "").
                            replace("org.aspectj.lang.JoinPoint thisJoinPoint", "");
                    crossRefAdvice.append("  pointcut ").append(this.methodDecl.ident()).append(pcParameters).append(": ");
                    crossRefAdvice.append("(" + xcsPointcut + ")").append(util.toString()).append(";\n");
                    crossRefAdvice.append("  Object around");
                    crossRefAdvice.append(pcParameters).append(": ");
                    String paramNames = methParamNames;
                    // handling the thisJoinPoint declaration
                    paramNames = paramNames.replace("thisJoinPoint, ", "").replace(", thisJoinPoint", "").replace("thisJoinPoint", "");
                    crossRefAdvice.append(this.methodDecl.ident() + paramNames).append(" && if(advise){return null;}\n");
                    AspectUtil.getInstance().appendCrossrefPointcut(crossRefAdvice.toString());
//					System.out.println("crossRefAdvice = "+crossRefAdvice);
                }
            }
        } else {
            classQualifiedName = AspectUtil.replaceDollaSymbol(classQualifiedName);
        }
        if (assertionMethType.equals("PreconditionAssertionMethod")) {
            codeStr = this.buildPreconditionAdviceHeader(classQualifiedName, methodQualifiedName,
                    instrumentationType, visibility, methodQualifiedNameJP, isMethodCrosscutSpecChecking, xcsPointcut, isXCSPointcutStatic);
        } else if (assertionMethType.equals("NPAndXPAssertionMethodsWithAroundAdvice")) {
            codeStr = this.buildNPAndXPAroundAdviceHeader(this.methodDecl.parameters(), classQualifiedName, methodQualifiedName,
                    instrumentationType, visibility, methodQualifiedNameJP, isMethodCrosscutSpecChecking, xcsPointcut, isXCSPointcutStatic);
        } else if (assertionMethType.equals("NPAssertionMethodWithAfterReturningAdvice")) {
            codeStr = this.buildNPAfterReturningAdviceHeader(this.methodDecl.parameters(), classQualifiedName, methodQualifiedName,
                    instrumentationType, visibility, isMethodCrosscutSpecChecking, xcsPointcut, isXCSPointcutStatic);
        } else if (assertionMethType.equals("XPAssertionMethodWithAfterThrowingAdvice")) {
            codeStr = this.buildXPAfterThrowingAdviceHeader(this.methodDecl.parameters(), classQualifiedName, methodQualifiedName,
                    instrumentationType, visibility, isMethodCrosscutSpecChecking, xcsPointcut, isXCSPointcutStatic);
        }
        code.append(AspectUtil.processMethSig(codeStr));
        return code;
    }

    private String processingXCSPointcut(String xcsParentClassName,
                                         String xcsParentClassFullyQualifiedName, Annotation adviceAnno,
                                         String xcsPCTmp, boolean flexibleXCS) {

        Pattern ownerTypePattern = Pattern.compile("\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b");
        Matcher ownerTypeMatcher = ownerTypePattern.matcher(xcsPCTmp);
        if (ownerTypeMatcher.find()) {
            xcsPCTmp = xcsPCTmp.replaceAll("\\b" + Pattern.quote(xcsParentClassFullyQualifiedName) + "\\b", xcsParentClassName);
        }
        ownerTypePattern = Pattern.compile("\\b" + Pattern.quote(xcsParentClassName) + "\\b");
        ownerTypeMatcher = ownerTypePattern.matcher(xcsPCTmp);
        if (ownerTypeMatcher.find()) {
            xcsPCTmp = xcsPCTmp.replaceAll("\\b" + Pattern.quote(xcsParentClassName) + "\\b", xcsParentClassFullyQualifiedName);
        }
        if (!flexibleXCS) {
            Pattern thisPattern = Pattern.compile("this(\\s)*\\((\\s)*");
            Matcher thisMatcher = thisPattern.matcher(xcsPCTmp);
            if (thisMatcher.find()) {
                JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), adviceAnno.getLineNumber()),
                        JmlMessages.INVALID_POINTCUT_THIS, this.methodDecl.ident());
                System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
            }

            // handling target pointcut/designator
            Pattern targetPattern = Pattern.compile("target(\\s)*\\((\\s)*");
            Matcher targetMatcher = targetPattern.matcher(xcsPCTmp);
            if (targetMatcher.find()) {
                JmlRacGenerator.fail(TokenReference.build(this.methodDecl.getTokenReference().file(), adviceAnno.getLineNumber()),
                        JmlMessages.INVALID_POINTCUT_TARGET, this.methodDecl.ident());
                System.exit(0); // just because of the duplication of error messages ... [[[hemr]]]
            }
        }
        // handling this pointcut/designator

        return xcsPCTmp;
    }

    private String buildNPAndXPAroundAdviceHeader(JFormalParameter[] parameters, String classQualifiedName,
                                                  String methodQualifiedName, String instrumentationType, long visibility, String methodQualifiedNameJP,
                                                  boolean isMethodCrosscutSpecChecking, String xcsPointcut, boolean isXCSPointcutStatic) {
        StringBuffer code = new StringBuffer("");
        String packageQualifiedName = this.methodDecl.getMethod().owner().packageName().replace("/", ".");
        JavaMethod jm = AspectUtil.getInstance().getCorrespondingJavaMethodThroughJMLMethod(this.methodDecl.getMethod().owner().getJavaName(), this.methodDecl);
        String methodReturnType = "";
        if ((jm != null) && (!(this.methodDecl.isConstructor()))) {
            if (jm.getReturnType().toString().equals(this.methodDecl.returnType().toString())) {
                methodReturnType = this.methodDecl.returnType().toString();
            } else {
                methodReturnType = jm.getReturnType().toString();
            }
        } else {
            methodReturnType = this.methodDecl.returnType().toString();
        }

        code.append("\n");
        if (this.javadoc != null) {
            if (instrumentationType.equals("clientAwareChecking")) {
                if (visibility == ACC_PUBLIC) {
                    code.append(this.javadoc.replace("postcondition", "public postcondition"));
                } else if (visibility == ACC_PROTECTED) {
                    code.append(this.javadoc.replace("postcondition", "protected postcondition"));
                } else if (visibility == 0L) { //default
                    code.append(this.javadoc.replace("postcondition", "default postcondition"));
                } else if (visibility == ACC_PRIVATE) {
                    code.append(this.javadoc.replace("postcondition", "private postcondition"));
                }
            } else {
                code.append(this.javadoc);
            }
        } else {
            code.append("/** Generated by JML to check assertions. */");
        }
        code.append("\n");

        if (isMethodCrosscutSpecChecking) {
            if (isXCSPointcutStatic) {
                code.append("java.lang.Object").append(" ").append("around (");
            } else {
                code.append("java.lang.Object").append(" ").append("around (final ").append(classQualifiedName).append(" ").append("object$rac");
            }
            code.append(generateAdviceMethodParameters(parameters, isXCSPointcutStatic, isMethodCrosscutSpecChecking,
                    AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            code.append(")");
//            code.append(this.generateMethodThrowsList(exceptionsInSignalsClauses));
            code.append(" :");
            code.append("\n");
            if (instrumentationType.equals("clientAwareChecking")) {
                String call = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
                AspectUtil.getInstance().appendPreconditionPointcut(call);
                code.append("   (").append(xcsPointcut).append(")");
                if (visibility == ACC_PROTECTED) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                } else if (visibility == 0L) {//package
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                } else if (visibility == ACC_PRIVATE) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + classQualifiedName + ")");
                }
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else if (instrumentationType.equals("callSite")) {
                String call = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
                AspectUtil.getInstance().appendPreconditionPointcut(call);
                code.append("   (").append(xcsPointcut).append(")");
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else {
                String execution = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
                AspectUtil.getInstance().appendPreconditionPointcut(execution);
                code.append("   (").append(xcsPointcut).append(")");
            }
            if (!isXCSPointcutStatic) {
                code.append(" && ");
                code.append("\n");
                code.append("   target(object$rac)");
            }

            // appending pointcut for utilprecondition checkingXCS --- [[[hemr]]]
            String pc = "";
            if (instrumentationType.equals("clientAwareChecking")) {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            } else if (instrumentationType.equals("callSite")) {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            } else {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            }
            AspectUtil.getInstance().appendPreconditionPointcut(pc);

        } // end of isMethodCrosscuttingSpecChecking
        else {
            String adviceexecution = "";
            String ifPC = "";
            if (AspectUtil.getInstance().isAspectAdvice(this.methodDecl)) {
                adviceexecution = " || (adviceexecution(";
                String methodNameWithParameterTypes = methodDecl.ident() + AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
                ifPC = " && if(JMLChecker.getThisJoinPointPartialMethSig(thisJoinPoint.getSignature().toLongString(), " +
                        "thisJoinPoint.getSignature().getDeclaringTypeName()).endsWith(\"" + methodNameWithParameterTypes + "\"))))";

            }
            if (this.isStatic) {
                code.append(methodReturnType).append(" ").append("around (");
                code.append(generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                        AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                code.append(")");
//	            code.append(this.generateMethodThrowsList(this.methodDecl.getExceptions()));
            } else {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (this.methodDecl.isConstructor()) {
                        code.append(classQualifiedName).append(" ").append("around (");
                        code.append(generateAdviceMethodParameters(parameters, true, isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                        code.append(")");
//						code.append(this.generateMethodThrowsList(this.methodDecl.getExceptions()));
                    } else {
                        code.append(methodReturnType).append(" ").append("around (final ").append(classQualifiedName).append(" ").append("object$rac");
                        code.append(generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                        code.append(")");
//						code.append(this.generateMethodThrowsList(this.methodDecl.getExceptions()));
                    }
                } else {
                    code.append(methodReturnType).append(" ").append("around (final ").append(classQualifiedName).append(" ").append("object$rac");
                    code.append(generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                            AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                    code.append(")");
//					code.append(this.generateMethodThrowsList(this.methodDecl.getExceptions()));
                }
            }
            code.append(" :");
            code.append("\n");
            if (this.methodDecl.isConstructor()) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append(methodQualifiedName).append(")");
                }
            } else if (this.isStatic) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                }
            } else {
                if (instrumentationType.equals("clientAwareChecking")) {
                    String call = "(call(" + methodReturnType + " " + methodQualifiedNameJP + "(" + AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString() + "))" + adviceexecution + ")";
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                    AspectUtil.getInstance().appendPreconditionPointcut(call);
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    String call = "(call(" + methodReturnType + " " + methodQualifiedNameJP + "(" + AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString() + "))" + adviceexecution + ")";
                    AspectUtil.getInstance().appendPreconditionPointcut(call);
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").
                            append(")").append(adviceexecution).append(")").append(ifPC);
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    String execution = "(execution(" + methodReturnType + " " + methodQualifiedNameJP + "(" + AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString() + "))" + adviceexecution + ")";
                    AspectUtil.getInstance().appendPreconditionPointcut(execution);
                    code.append("   (execution(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").
                            append(")").append(adviceexecution).append(")").append(ifPC);
                }
            }
            if (!this.isStatic) {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (!this.methodDecl.isConstructor()) {
                        code.append("\n");
                        code.append("   && ");
                        code.append("target(object$rac)");
                    }
                } else {
                    code.append("\n");
                    code.append("   && ");
                    code.append("this(object$rac)");
                }
            }
        }

        if (!isMethodCrosscutSpecChecking) {
            this.generateMethodArgsForTheAdvice(parameters, code, AspectUtil.getInstance().isAspectAdvice(this.methodDecl));
        }
        String result = code.toString();
        return result;
    }

    /**
     * @param code
     * @param parameters
     * @param classQualifiedName
     * @param methodQualifiedName
     */
    private String buildNPAfterReturningAdviceHeader(JFormalParameter[] parameters, String classQualifiedName,
                                                     String methodQualifiedName, String instrumentationType, long visibility, boolean isMethodCrosscutSpecChecking, String xcsPointcut, boolean isXCSPointcutStatic) {
        StringBuffer code = new StringBuffer("");
        String packageQualifiedName = this.methodDecl.getMethod().owner().packageName().replace("/", ".");
        JavaMethod jm = AspectUtil.getInstance().getCorrespondingJavaMethodThroughJMLMethod(this.methodDecl.getMethod().owner().getJavaName(), this.methodDecl);
        String methodReturnType = "";
        if ((jm != null) && (!(this.methodDecl.isConstructor()))) {
            if (jm.getReturnType().toString().equals(this.methodDecl.returnType().toString())) {
                methodReturnType = this.methodDecl.returnType().toString();
            } else {
                methodReturnType = jm.getReturnType().toString();
            }
        } else {
            methodReturnType = this.methodDecl.returnType().toString();
        }

        code.append("\n");
        if (this.javadoc != null) {
            if (instrumentationType.equals("clientAwareChecking")) {
                if (visibility == ACC_PUBLIC) {
                    code.append(this.javadoc.replace("postcondition", "public postcondition"));
                } else if (visibility == ACC_PROTECTED) {
                    code.append(this.javadoc.replace("postcondition", "protected postcondition"));
                } else if (visibility == 0L) { //default
                    code.append(this.javadoc.replace("postcondition", "default postcondition"));
                } else if (visibility == ACC_PRIVATE) {
                    code.append(this.javadoc.replace("postcondition", "private postcondition"));
                }
            } else {
                code.append(this.javadoc);
            }
        } else {
            code.append("/** Generated by JML to check assertions. */");
        }
        code.append("\n");

        if (isMethodCrosscutSpecChecking) {
            if (isXCSPointcutStatic) {
                code.append("after (");
            } else {
                code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");
            }
            code.append(this.generateAdviceMethodParameters(parameters, isXCSPointcutStatic, isMethodCrosscutSpecChecking,
                    AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            code.append(")").append(" returning (final ").append("java.lang.Object").append(" rac$result) :");
            if (instrumentationType.equals("clientAwareChecking")) {
                code.append("   (").append(xcsPointcut).append(")");
                if (visibility == ACC_PROTECTED) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                } else if (visibility == 0L) {//package
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                } else if (visibility == ACC_PRIVATE) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + classQualifiedName + ")");
                }
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else if (instrumentationType.equals("callSite")) {
                code.append("   (").append(xcsPointcut).append(")");
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else {
                code.append("   (").append(xcsPointcut).append(")");
            }
            if (!isXCSPointcutStatic) {
                code.append(" && ");
                code.append("\n");
                code.append("   target(object$rac)");
            }
        } // end crosscuting spec checking
        else {
            String adviceexecution = "";
            String ifPC = "";
            if (AspectUtil.getInstance().isAspectAdvice(this.methodDecl)) {
                adviceexecution = " || (adviceexecution(";
                String methodNameWithParameterTypes = methodDecl.ident() + AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
                ifPC = " && if(JMLChecker.getThisJoinPointPartialMethSig(thisJoinPoint.getSignature().toLongString(), " +
                        "thisJoinPoint.getSignature().getDeclaringTypeName()).endsWith(\"" + methodNameWithParameterTypes + "\"))))";

            }
            if (this.isStatic) {
                code.append(" ").append("after (");
                code.append(this.generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                        AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            } else {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (this.methodDecl.isConstructor()) {
                        code.append("after (");
                        code.append(this.generateAdviceMethodParameters(parameters, true, isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                    } else {
                        code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");
                        code.append(this.generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                    }
                } else {
                    code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");
                    code.append(this.generateAdviceMethodParameters(parameters, this.isStatic, isMethodCrosscutSpecChecking,
                            AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                }
            }
            if (methodReturnType.equals("void")) {
                if (this.methodDecl.isConstructor() && (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking"))) {
                    code.append(")").append(" returning (final " + classQualifiedName + " object$rac) : ");
                } else {
                    code.append(")").append(" returning () :");
                }
            } else {
                code.append(")").append(" returning (final " + this.methodDecl.returnType() + " rac$result) :");
            }
            code.append("\n");
            if (this.methodDecl.isConstructor()) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append(methodQualifiedName).append(")");
                }
            } else if (this.isStatic) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                }
            } else {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   (execution(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                }
            }
            if (!this.isStatic) {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (!this.methodDecl.isConstructor()) {
                        code.append(" && ");
                        code.append("target(object$rac)");
                    }
                } else {
                    code.append(" && ");
                    code.append("this(object$rac)");
                }
            }
        }

        if (!isMethodCrosscutSpecChecking) {
            this.generateMethodArgsForTheAdvice(parameters, code, AspectUtil.getInstance().isAspectAdvice(this.methodDecl));
        }
        String result = code.toString();
        return result;
    }

    /**
     * @param code
     * @param parameters
     * @param classQualifiedName
     * @param methodQualifiedName
     */
    private String buildXPAfterThrowingAdviceHeader(JFormalParameter[] parameters, String classQualifiedName,
                                                    String methodQualifiedName, String instrumentationType, long visibility, boolean isMethodCrosscutSpecChecking,
                                                    String xcsPointcut, boolean isXCSPointcutStatic) {
        StringBuffer code = new StringBuffer("");
        String packageQualifiedName = this.methodDecl.getMethod().owner().packageName().replace("/", ".");
        JavaMethod jm = AspectUtil.getInstance().getCorrespondingJavaMethodThroughJMLMethod(this.methodDecl.getMethod().owner().getJavaName(), this.methodDecl);
        String methodReturnType = "";
        if ((jm != null) && (!(this.methodDecl.isConstructor()))) {
            if (jm.getReturnType().toString().equals(this.methodDecl.returnType().toString())) {
                methodReturnType = this.methodDecl.returnType().toString();
            } else {
                methodReturnType = jm.getReturnType().toString();
            }
        } else {
            methodReturnType = this.methodDecl.returnType().toString();
        }

        code.append("\n");
        if (this.javadoc != null) {
            if (instrumentationType.equals("clientAwareChecking")) {
                if (visibility == ACC_PUBLIC) {
                    code.append(this.javadoc.replace("postcondition", "public postcondition"));
                } else if (visibility == ACC_PROTECTED) {
                    code.append(this.javadoc.replace("postcondition", "protected postcondition"));
                } else if (visibility == 0L) { //default
                    code.append(this.javadoc.replace("postcondition", "default postcondition"));
                } else if (visibility == ACC_PRIVATE) {
                    code.append(this.javadoc.replace("postcondition", "private postcondition"));
                }
            } else {
                code.append(this.javadoc);
            }
        } else {
            code.append("/** Generated by JML to check assertions. */");
        }
        code.append("\n");

        if (isMethodCrosscutSpecChecking) {
            if (isXCSPointcutStatic) {
                code.append("after (");
            } else {
                code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");
            }
            code.append(this.generateAdviceMethodParameters(parameters, isXCSPointcutStatic, isMethodCrosscutSpecChecking,
                    AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            code.append(")").append(" throwing (Throwable rac$e)");
//			code.append(this.generateMethodThrowsList(exceptionsInSignalsClauses));
            code.append(" :");
            code.append("\n");
            if (instrumentationType.equals("clientAwareChecking")) {
                code.append("   (").append(xcsPointcut).append(")");
                if (visibility == ACC_PROTECTED) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                } else if (visibility == 0L) {//package
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                } else if (visibility == ACC_PRIVATE) {
                    code.append(" && ");
                    code.append("\n");
                    code.append("   within(" + classQualifiedName + ")");
                }
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else if (instrumentationType.equals("callSite")) {
                code.append("   (").append(xcsPointcut).append(")");
                code.append(" && ");
                code.append("\n");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else {
                code.append("   (").append(xcsPointcut).append(")");
            }
            if (!isXCSPointcutStatic) {
                code.append(" && ");
                code.append("\n");
                code.append("   target(object$rac)");
            }
        } // end crosscutting spec checking
        else {
            String adviceexecution = "";
            String ifPC = "";
            if (AspectUtil.getInstance().isAspectAdvice(this.methodDecl)) {
                adviceexecution = " || (adviceexecution(";
                String methodNameWithParameterTypes = methodDecl.ident() + AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
                ifPC = " && if(JMLChecker.getThisJoinPointPartialMethSig(thisJoinPoint.getSignature().toLongString(), " +
                        "thisJoinPoint.getSignature().getDeclaringTypeName()).endsWith(\"" + methodNameWithParameterTypes + "\"))))";

            }
            if (this.isStatic) {
                code.append(" ").append("after (");
                code.append(this.generateAdviceMethodParameters(parameters, this.methodDecl.isStatic(), isMethodCrosscutSpecChecking,
                        AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            } else {
                if ((instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) && (this.methodDecl.isConstructor())) {
                    code.append("after (");
                    code.append(this.generateAdviceMethodParameters(parameters, true, isMethodCrosscutSpecChecking,
                            AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                } else {
                    code.append("after (final ").append(classQualifiedName).append(" ").append("object$rac");
                    code.append(this.generateAdviceMethodParameters(parameters, this.methodDecl.isStatic(), isMethodCrosscutSpecChecking,
                            AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                }
            }
            code.append(")").append(" throwing (Throwable rac$e) :");
            code.append("\n");
            if (this.methodDecl.isConstructor()) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append(methodQualifiedName).append(")");
                }
            } else if (this.isStatic) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).append(")").append(")");
                }
            } else {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   (execution(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").append(AspectUtil.generateMethodParametersForAdvicePointcut(parameters).toString()).
                            append(")").append(")").append(adviceexecution).append(")").append(ifPC);
                }
            }
            if (!this.isStatic) {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (!this.methodDecl.isConstructor()) {
                        code.append(" && ");
                        code.append("target(object$rac)");
                    }
                } else {
                    code.append(" && ");
                    code.append("this(object$rac)");
                }
            }
        }

        if (!isMethodCrosscutSpecChecking) {
            this.generateMethodArgsForTheAdvice(parameters, code, AspectUtil.getInstance().isAspectAdvice(this.methodDecl));
        }
        String result = code.toString();
        return result;
    }

//	private String generateMethodThrowsList(CClassType[] exceptions) {
//		StringBuffer code = new StringBuffer("");
//		if(exceptions != null){
//			if(exceptions.length > 0){
//				code.append(" ");
//				code.append("throws ");
//			}
//			for (int i = 0; i < exceptions.length; i++) {
//				if (i != 0)
//					code.append(", ");
//				String ident = exceptions[i].qualifiedName().replace("/", ".").replace("$", ".");
//				code.append(ident);
//			}	
//		}
//		return code.toString();
//	}

//	private String generateMethodThrowsList(List<CType> exceptionsInSignalsClauses) {
//		StringBuffer code = new StringBuffer("");
//		if(exceptionsInSignalsClauses.size() > 0){
//			code.append(" ");
//			code.append("throws ");
//			int i = 0;
//			for (Iterator<CType> iterator = exceptionsInSignalsClauses.iterator(); iterator
//					.hasNext();) {
//				if (i != 0)
//					code.append(", ");
//				CType cType = iterator.next();
//				code.append(cType);
//				i++;
//				
//			}
//		}
//		return code.toString();
//	}

    protected String buildAssertionMethodCall(String methodName, String ownerType,
                                              JFormalParameter[] parameters, CClassType[] exceptions, String assertionMethodType) {
        final StringBuffer code = new StringBuffer();
        code.append(methodName);

        // formal parameters
        code.append("(");
        if (parameters != null) {
            for (int i = 0; i < parameters.length; i++) {
                if (i != 0)
                    code.append(", ");

                parameters[i].accept(new JmlAbstractVisitor() {
                    public void visitJmlFormalParameter(
                            JmlFormalParameter self) {
                        String ident = self.ident();
                        code.append(ident);
                    }
                });
            }
        }
        if (assertionMethodType.equals("NormalPostconditionAssertionMethod")) {
            if (this.parameters != null && this.parameters.length > 0) {
                code.append(", ");
            }
            code.append(" ").append("rac$result");
        }
        if (assertionMethodType.equals("ExceptionalPostconditionAssertionMethod")) {
            if (this.parameters != null && this.parameters.length > 0) {
                code.append(", ");
            }
            code.append(" ").append("rac$e");
        }

        if (Main.aRacOptions.clientAwareChecking()) {
            if (this.parameters != null && this.parameters.length > 0) {
                code.append(", ");
            }
            code.append("object$rac");
        }

        code.append(")");

        return code.toString();
    }

    /**
     * @return
     */
    protected String generateErrorMessage(String context, String tokenReference, String errorType, boolean isMethodCrosscutSpecChecking) {
        String result = "";

        if ((errorType.equals("Precondition_Error"))
                || (errorType.equals("Precondition_EvaluationError"))
                || (errorType.equals("XPost_Error"))) {
            result = this.generatePreAndXPostErrorMessage(context,
                    tokenReference, errorType, isMethodCrosscutSpecChecking);
        } else if ((errorType.equals("NormalPostconditionError"))
                || (errorType.equals("NPost_EvaluationError"))) {
            result = this.generateNPostErrorMessage(context, tokenReference,
                    errorType, isMethodCrosscutSpecChecking);
        }
        return result;
    }

    /**
     * @param context
     * @param errorType
     * @return
     */
    private String generatePreAndXPostErrorMessage(String context,
                                                   String tokenReference, String errorType, boolean isMethodCrosscutSpecChecking) {
//		List inheritedMethsWithPreITD = getMethsWithPreITDChecking();
//		String inheritedPreFromSuperTypes = "";
        String methodDescription = "";
        if (isMethodCrosscutSpecChecking) {
            methodDescription = "by method \"+thisJoinPoint.getSignature().getDeclaringTypeName()+\".\"+thisJoinPoint.getSignature().getName()+\"";
        } else {
            methodDescription = "by method " + this.methodDecl.getMethod().getJavaName();
        }
        String evalErrorDescription = AssertionMethod.SPEC_EVAL_ERROR_MSG;
        final String SPEC_ERROR_MSG = AssertionMethod.SPEC_ERROR_MSG;
        final String CODE_ERROR_MSG = AssertionMethod.CODE_ERROR_MSG;
        final String NONE = "";
        String result = "";

        // resolving inherited precondition...
//		inheritedPreFromSuperTypes = this.getInheritedPreFromSuperTypes(
//				inheritedMethsWithPreITD, inheritedPreFromSuperTypes);

        if (this.methodDecl.body() != null) {
            JStatement js[] = null;

            try {
                js = this.methodDecl.body().body();

                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContext =
                        (js.length == 0 ? "\"" :
                                ", line " +
                                        +js[0].getTokenReference().line() + " ("
                                        + this.typeDecl.getCClass().getJavaName() + ".java:"
                                        + js[0].getTokenReference().line() + ")\"");
                String bodyCodeReferenceWithContext = bodyCodeReferenceWithoutContext + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                String bodyCodeReferenceWithoutContextForXPost =
                        (js.length == 0 ? "\"" :
                                ", line " +
                                        +js[js.length - 1].getTokenReference().line() + " ("
                                        + this.typeDecl.getCClass().getJavaName() + ".java:"
                                        + js[js.length - 1].getTokenReference().line() + ")\"");

                String bodyCodeReferenceWithContextForXPost = bodyCodeReferenceWithoutContextForXPost + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                if (errorType.equals("Precondition_EvaluationError")) {
                    //result = evalErrorDescription + this.typeDecl.ident() + ".java\\\"" + bodyCodeReferenceWithoutContext;
                    if (!tokenReference.equals(NONE)) {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n\"" + context + "+\"" : "") + "\\nCaused by: \"";
                    } else {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                    }

                } else if (errorType.equals("Precondition_Error")) {
                    String tmp = "";

                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                        if ((js.length == 0) && (context.length() > 0)) {
                            result = result + "+ \", when \\n\"" + context;
                        }
                    }

                } else if (errorType.equals("XPost_Error")) {
                    String tmp = "";
                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContextForXPost;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContextForXPost;
                    }

                    if ((js.length == 0) && (context.length() > 0)) {
                        result = result + "+ \", when \\n\"" + context;
                    }
                }
            } catch (NullPointerException e) {
                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContext = "\"";
                String bodyCodeReferenceWithContext = bodyCodeReferenceWithoutContext + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                String bodyCodeReferenceWithoutContextForXPost = "\"";

                String bodyCodeReferenceWithContextForXPost = bodyCodeReferenceWithoutContextForXPost + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                if (errorType.equals("Precondition_EvaluationError")) {
                    //result = evalErrorDescription + this.typeDecl.ident() + ".java\\\"" + bodyCodeReferenceWithoutContext;
                    if (!tokenReference.equals(NONE)) {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n\"" + context + "+\"" : "") + "\\nCaused by: \"";
                    } else {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                    }

                } else if (errorType.equals("Precondition_Error")) {
                    String tmp = "";
                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                        if (((context.length() > 0))) {
                            result = result + "+ \", when \\n\"" + context;
                        }
                    }
                } else if (errorType.equals("XPost_Error")) {
                    String tmp = "";
                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContextForXPost;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContextForXPost;
                    }

                    if ((context.length() > 0)) {
                        // never throw an exception... so it is not necessary to create context msg... (henrique rebelo)
                        result = "\"\"";
                    }
                }
            }
        } else {
            // If has no body, which occurs with methods inside Interfaces, the only possibility here is "XPost_Error"
            // because for preconditions, only intertype declarations are generated... (there is no precondition_error code generated)

            if (errorType.endsWith("_Error")) {
                String tmp = "";
                result = "\""
                        + (!tokenReference.equals(NONE) ? ", " + tokenReference
                        + ", and \\n" + methodDescription
                        + CODE_ERROR_MSG + "File \\\""
                        + this.typeDecl.getCClass().getJavaName()
                        + ".java\\\"" : "")
                        + methodDescription
                        + SPEC_ERROR_MSG
                        + "File \\\""
                        + this.typeDecl.getCClass().getJavaName()
                        + ".java\\\""
                        + (context.length() > 0 ? ", when \\n" + context : "\"");
            }

            if (errorType.equals("Precondition_EvaluationError")) {
                if (!tokenReference.equals(NONE)) {
                    result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n\"+\"" + context + "+\"" : "") + "\\nCaused by: \"";
                } else {
                    result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                }

            }
        }

        return result;
    }


    private String generateNPostErrorMessage(String context,
                                             String tokenReference, String errorType, boolean isMethodCrosscutSpecChecking) {
        String methodDescription = "";
        if (isMethodCrosscutSpecChecking) {
            methodDescription = "by method \"+thisJoinPoint.getSignature().getDeclaringTypeName()+\".\"+thisJoinPoint.getSignature().getName()+\"";
        } else {
            methodDescription = "by method " + this.methodDecl.getMethod().getJavaName();
        }
        String evalErrorDescription = AssertionMethod.SPEC_EVAL_ERROR_MSG;
        final String SPEC_ERROR_MSG = AssertionMethod.SPEC_ERROR_MSG;
        final String CODE_ERROR_MSG = AssertionMethod.CODE_ERROR_MSG;
        final String NONE = "";
        String result = "";

        if (this.methodDecl.body() != null) {
            JStatement js[] = null;

            try {
                js = this.methodDecl.body().body();
                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContext =
                        (js.length == 0 ? "\"" :
                                ", line " +
                                        +js[js.length - 1].getTokenReference().line() + " ("
                                        + this.typeDecl.getCClass().getJavaName() + ".java:"
                                        + js[js.length - 1].getTokenReference().line() + ")\"");
                String bodyCodeReferenceWithContext = bodyCodeReferenceWithoutContext + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                if (errorType.equals("NPost_EvaluationError")) {
                    if (!tokenReference.equals(NONE)) {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n\"" + context + "+\"" : "") + "\\nCaused by: \"";
                    } else {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                    }
                } else {
                    String tmp = "";
                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                        if ((js.length == 0) && (context.length() > 0)) {
                            result = result + "+\", when \\n\"" + context;
                        }
                    }
                }
            } catch (NullPointerException e) {
                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContext = "\"";

                String bodyCodeReferenceWithContext = bodyCodeReferenceWithoutContext + (context.length() > 0 ? "+\", when \\n\"" + context : "");

                if (errorType.equals("NPost_EvaluationError")) {
                    if (!tokenReference.equals(NONE)) {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n\"" + context + "+\"" : "") + "\\nCaused by: \"";
                    } else {
                        result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                    }
                } else {
                    String tmp = "";
                    if (!tokenReference.equals(NONE)) {
                        tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                    } else {
                        tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                        result += tmp + bodyCodeReferenceWithContext;
                        if ((context.length() > 0)) {
                            result = result + "+\", when \\n\"" + context;
                        }
                    }
                }
            }
        } else {
            if (errorType.equals("NPost_EvaluationError")) {
                if (!tokenReference.equals(NONE)) {
                    result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + " " + methodDescription + SPEC_ERROR_MSG + tokenReference + (context.length() > 0 ? "\"+\", when \\n" + context + "+\"" : "") + "\\nCaused by: \"";
                } else {
                    result = evalErrorDescription + this.typeDecl.getCClass().getJavaName() + ".java\\\"\\nCaused by: \"";
                }
            } else {
                if (!tokenReference.equals(NONE)) {
                    result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + ", " + tokenReference + (context.length() > 0 ? ", when \\n" + context : "\"");
                } else {
                    result = "\"" + methodDescription + " at \\n" + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"" + (context.length() > 0 ? ", when \\n" + context : "\"");
                }
            }
        }
        return result;
    }

    private String buildPreconditionAdviceHeader(String classQualifiedName, String methodQualifiedName, String instrumentationType,
                                                 long visibility, String methodQualifiedNameJP, boolean isMethodCrosscutSpecChecking, String xcsPointcut, boolean isXCSPointcutStatic) {
        StringBuffer code = new StringBuffer("");
        String packageQualifiedName = this.methodDecl.getMethod().owner().packageName().replace("/", ".");
        JavaMethod jm = AspectUtil.getInstance().getCorrespondingJavaMethodThroughJMLMethod(this.methodDecl.getMethod().owner().getJavaName(), this.methodDecl);
        String methodReturnType = "";
        if (jm != null && !this.methodDecl.isConstructor()) {
            if (jm.getReturnType().toString().equals(this.methodDecl.returnType().toString())) {
                methodReturnType = this.methodDecl.returnType().toString();
            } else {
                methodReturnType = jm.getReturnType().toString();
            }
        } else {
            methodReturnType = this.methodDecl.returnType().toString();
        }
        code.append("\n");
        if (this.javadoc != null) {
            if (instrumentationType.equals("clientAwareChecking")) {
                if (visibility == ACC_PUBLIC) {
                    code.append(this.javadoc.replace("precondition", "public precondition"));
                } else if (visibility == ACC_PROTECTED) {
                    code.append(this.javadoc.replace("precondition", "protected precondition"));
                } else if (visibility == 0L) { //default
                    code.append(this.javadoc.replace("precondition", "default precondition"));
                } else if (visibility == ACC_PRIVATE) {
                    code.append(this.javadoc.replace("precondition", "private precondition"));
                }
            } else {
                code.append(this.javadoc);
            }
        } else {
            code.append("/** Generated by JML to check assertions. */");
        }
        code.append("\n");
        if (isMethodCrosscutSpecChecking) {
            if (isXCSPointcutStatic) {
                code.append("before (");
            } else {
                code.append("before (final ").append(classQualifiedName).append(" ").append("object$rac");
            }
            code.append(this.generateAdviceMethodParameters(this.parameters, isXCSPointcutStatic, isMethodCrosscutSpecChecking,
                    AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            code.append(")").append(" :");
            code.append("\n");
            if (instrumentationType.equals("clientAwareChecking")) {
                code.append("   (").append(xcsPointcut).append(")").append(" && ");
                if (visibility == ACC_PROTECTED) {
                    code.append("\n");
                    code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    code.append(" && ");
                } else if (visibility == 0L) {//package
                    code.append("\n");
                    code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    code.append(" && ");
                } else if (visibility == ACC_PRIVATE) {
                    code.append("\n");
                    code.append("   within(" + classQualifiedName + ")");
                    code.append(" && ");
                }
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else if (instrumentationType.equals("callSite")) {
                code.append("   (").append(xcsPointcut).append(")").append(" && ");
                code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
            } else {
                code.append("   (").append(xcsPointcut).append(")");
            }
            if (!isXCSPointcutStatic) {
                code.append(" && ");
                code.append("\n");
                code.append("   target(object$rac)");
            }

            // appending pointcut for utilprecondition checkingXCS --- [[[hemr]]]
            String pc = "";
            if (instrumentationType.equals("clientAwareChecking")) {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            } else if (instrumentationType.equals("callSite")) {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            } else {
                pc = isXCSPointcutStatic ? "(" + xcsPointcut + ")" : "(" + xcsPointcut + ") && target(" + classQualifiedName + ")";
            }
            AspectUtil.getInstance().appendPreconditionPointcut(pc);

        } // end isMethodCrosscutingSpecChecking
        else {
            String adviceexecution = "";
            String ifPC = "";
            if (AspectUtil.getInstance().isAspectAdvice(this.methodDecl)) {
                adviceexecution = " || (adviceexecution(";
                String methodNameWithParameterTypes = methodDecl.ident() + AspectUtil.generateMethodParameters(methodDecl.parameters(), false).toString();
                ifPC = " && if(JMLChecker.getThisJoinPointPartialMethSig(thisJoinPoint.getSignature().toLongString(), " +
                        "thisJoinPoint.getSignature().getDeclaringTypeName()).endsWith(\"" + methodNameWithParameterTypes + "\"))))";

            }
            if (isStatic) {
                code.append("before (");
                code.append(this.generateAdviceMethodParameters(this.parameters, this.methodDecl.isStatic(), isMethodCrosscutSpecChecking,
                        AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
            } else {
                if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                    if (this.methodDecl.isConstructor()) {
                        code.append("before (");
                        code.append(this.generateAdviceMethodParameters(this.parameters, true, isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                    } else {
                        code.append("before (final ").append(classQualifiedName).append(" ").append("object$rac");
                        code.append(this.generateAdviceMethodParameters(this.parameters, this.methodDecl.isStatic(), isMethodCrosscutSpecChecking,
                                AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                    }
                } else {
                    code.append("before (final ").append(classQualifiedName).append(" ").append("object$rac");
                    code.append(this.generateAdviceMethodParameters(this.parameters, this.methodDecl.isStatic(), isMethodCrosscutSpecChecking,
                            AspectUtil.getInstance().isAspectAdvice(this.methodDecl)).toString());
                }
            }
            code.append(") :\n");

            if (this.methodDecl.isConstructor()) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append(methodQualifiedName).append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + packageQualifiedName + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append(methodQualifiedName).append(")").append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append(methodQualifiedName).append(")").append(" && ");
                    code.append("\n");
                    code.append("   this(object$rac)");
                }
            } else if (this.isStatic) {
                if (instrumentationType.equals("clientAwareChecking")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType.toString()).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")");
                    if (visibility == ACC_PROTECTED) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                    } else if (visibility == 0L) {//package
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append(" && ");
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                    }
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    code.append("   call(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    code.append("   execution(").append("static").append(" ").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")");
                }
            } else {
                if (instrumentationType.equals("clientAwareChecking")) {
                    String call = "(call(" + methodReturnType + " " + methodQualifiedNameJP +
                            "(" + AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString() + "))" + adviceexecution + ")" + ifPC;
                    AspectUtil.getInstance().appendPreconditionPointcut(call);
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")").
                            append(adviceexecution).append(")").append(ifPC).append(" && ");
                    if (visibility == ACC_PROTECTED) {
                        code.append("\n");
                        code.append("   (within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*) || within(" + classQualifiedName + "+))");
                        code.append(" && ");
                    } else if (visibility == 0L) {//package
                        code.append("\n");
                        code.append("   within(" + (packageQualifiedName.equals("") ? "" : packageQualifiedName) + "*)");
                        code.append(" && ");
                    } else if (visibility == ACC_PRIVATE) {
                        code.append("\n");
                        code.append("   within(" + classQualifiedName + ")");
                        code.append(" && ");
                    }
                    code.append("target(object$rac)");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else if (instrumentationType.equals("callSite")) {
                    String call = "(call(" + methodReturnType + " " + methodQualifiedNameJP +
                            "(" + AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString() + "))" + adviceexecution + ")" + ifPC;
                    AspectUtil.getInstance().appendPreconditionPointcut(call);
                    code.append("   (call(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")").
                            append(adviceexecution).append(")").append(ifPC).append(" && ");
                    code.append("\n");
                    code.append("   target(object$rac)");
                    code.append(" && ");
                    code.append("\n");
                    code.append("   !within(*..AspectJMLRac_*) && !within(AspectJMLRac_*)");
                } else {
                    String execution = "(execution(" + methodReturnType + " " + methodQualifiedNameJP +
                            "(" + AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString() + "))" + adviceexecution + ")" + ifPC;
                    AspectUtil.getInstance().appendPreconditionPointcut(execution);
                    code.append("   (execution(").append(methodReturnType).append(" ").append(methodQualifiedName).append("(").
                            append(AspectUtil.generateMethodParametersForAdvicePointcut(this.parameters).toString()).append(")").append(")").
                            append(adviceexecution).append(")").append(ifPC).append(" && \n");

                    code.append("   this(object$rac)");
                }
            }
        }
        if (!isMethodCrosscutSpecChecking) {
            this.generateMethodArgsForTheAdvice(parameters, code, AspectUtil.getInstance().isAspectAdvice(this.methodDecl));
        }
        String result = code.toString();
        return result;
    }

    /**
     * @param parameters
     * @param isStatic
     * @param code
     */
    private StringBuffer generateAdviceMethodParameters(JFormalParameter[] parameters,
                                                        boolean isStatic, final boolean isMethodCrosscutSpecChecking, final boolean isAspectAdvice) {
        final StringBuffer code = new StringBuffer("");
        if (parameters != null) {
            if (parameters.length > 0) {
                if ((this.methodDecl.isConstructor() && this.methodDecl.getMethod().owner().isInnerClass()) && !(isAspectAdvice)) {
                    if (!isStatic && parameters.length > 1)
                        code.append(", ");
                    for (int i = 1; i < parameters.length; i++) {
                        if (i != 1)
                            code.append(", ");
                        parameters[i].accept(new JmlAbstractVisitor() {
                            public void visitJmlFormalParameter(
                                    JmlFormalParameter self) {
                                CType actualType = self.getType();
                                String ident = self.ident();
                                if (AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)).equals("org.aspectj.lang.JoinPoint")) {
                                    if (ident.equals(VN_ASPECTJ_THISJOINPOINT)) {
                                        JmlRacGenerator.fail(self.getTokenReference(), JmlMessages.INVALID_JOINPOINT_ARG_IDENT, self.ident());
                                        System.exit(0);
                                    }
                                }
                                code.append("final ");
                                code.append(AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)));
                                code.append(" ");
                                code.append(ident);
                            }
                        });
                    }
                } else {
                    if (!isStatic) {
                        if (isMethodCrosscutSpecChecking || isAspectAdvice) {
                            if (parameters.length == 1) {
                                if (!TransUtils.toString(parameters[0].getType()).equals("org.aspectj.lang.JoinPoint")) {
                                    code.append(", ");
                                }
                            } else {
                                code.append(", ");
                            }
                        } else {
                            code.append(", ");
                        }
                    }
                    for (int i = 0; i < parameters.length; i++) {
                        if (i != 0)
                            code.append(", ");
                        parameters[i].accept(new JmlAbstractVisitor() {
                            public void visitJmlFormalParameter(
                                    JmlFormalParameter self) {
                                CType actualType = self.getType();
                                String ident = self.ident();
                                if (isMethodCrosscutSpecChecking || isAspectAdvice) {
                                    if (AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)).equals("org.aspectj.lang.JoinPoint")) {
                                        if (code.length() - 2 >= 0) {
                                            code.delete(code.length() - 2, code.length() - 1); // removing the comma...
                                        }
                                        if (!ident.equals(VN_ASPECTJ_THISJOINPOINT)) {
                                            JmlRacGenerator.fail(self.getTokenReference(), JmlMessages.INVALID_JOINPOINT_ARG_IDENT_XCS, self.ident());
                                            System.exit(0);
                                        }
                                    } else {
                                        code.append("final ");
                                        code.append(AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)));
                                        code.append(" ");
                                        code.append(ident);
                                    }
                                } else {
                                    if (!isAspectAdvice) {
                                        if (AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)).equals("org.aspectj.lang.JoinPoint")) {
                                            if (ident.equals(VN_ASPECTJ_THISJOINPOINT)) {
                                                JmlRacGenerator.fail(self.getTokenReference(), JmlMessages.INVALID_JOINPOINT_ARG_IDENT, self.ident());
                                                System.exit(0);
                                            }
                                        }
                                    }
                                    code.append("final ");
                                    code.append(AspectUtil.replaceDollaSymbol(TransUtils.toString(actualType)));
                                    code.append(" ");
                                    code.append(ident);
                                }
                            }
                        });
                    }
                }
            }
        }
        if (code.length() > 0) {
            // workaround to fix the ", ," if wrongly generated for params --- [[[hemr]]]
            if (code.toString().indexOf("") != -1) {
                String advParam = code.toString().replace(", ,", ",");
                code.delete(0, code.length());
                code.append(advParam);
            }
        }
        return code;
    }

    /**
     * @param parameters
     * @param code
     */
    private void generateMethodArgsForTheAdvice(JFormalParameter[] parameters,
                                                final StringBuffer code, final boolean isAspectAdvice) {
        if (parameters != null) {
            if (parameters.length > 0) {
                code.append(" && ").append("args(");
            }
            if (this.methodDecl.isConstructor() && this.methodDecl.getMethod().owner().isInnerClass()) {
                for (int i = 1; i < parameters.length; i++) {
                    if (i != 1)
                        code.append(", ");
                    parameters[i].accept(new JmlAbstractVisitor() {
                        public void visitJmlFormalParameter(
                                JmlFormalParameter self) {
                            String ident = self.ident();
                            if (ident.equals("thisJoinPoint") && isAspectAdvice) {
                                code.append("..");
                            } else {
                                code.append(ident);
                            }

                        }
                    });
                }
            } else {
                for (int i = 0; i < parameters.length; i++) {
                    if (i != 0)
                        code.append(", ");
                    parameters[i].accept(new JmlAbstractVisitor() {
                        public void visitJmlFormalParameter(
                                JmlFormalParameter self) {
                            String ident = self.ident();
                            if (ident.equals("thisJoinPoint") && isAspectAdvice) {
                                code.append("..");
                            } else {
                                code.append(ident);
                            }
                        }
                    });
                }
            }
            if (parameters.length > 0) {
                code.append(")");
			}
        }
    }

    protected HashMap getPreconditions(long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            return AspectUtil.getInstance().publicPreconditionSpecCases;
        } else if (visibility == Constants.ACC_PROTECTED) {
            return AspectUtil.getInstance().protectedPreconditionSpecCases;
        } else if (visibility == 0L) { //default
            return AspectUtil.getInstance().defaultPreconditionSpecCases;
        } else if (visibility == Constants.ACC_PRIVATE) {
            return AspectUtil.getInstance().privatePreconditionSpecCases;
        } else {
            return AspectUtil.getInstance().preconditionSpecCases;
        }
    }

    protected HashMap getNormalPostconditions(long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            return AspectUtil.getInstance().publicNPostconditionSpecCases;
        } else if (visibility == Constants.ACC_PROTECTED) {
            return AspectUtil.getInstance().protectedNPostconditionSpecCases;
        } else if (visibility == 0L) { //default
            return AspectUtil.getInstance().defaultNPostconditionSpecCases;
        } else if (visibility == Constants.ACC_PRIVATE) {
            return AspectUtil.getInstance().privateNPostconditionSpecCases;
        } else {
            return AspectUtil.getInstance().nPostconditionSpecCases;
        }
    }

    protected HashMap getContextForNPost(long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            return AspectUtil.getInstance().publicNPostconditionForContextSpecCases;
        } else if (visibility == Constants.ACC_PROTECTED) {
            return AspectUtil.getInstance().protectedNPostconditionForContextSpecCases;
        } else if (visibility == 0L) { //default
            return AspectUtil.getInstance().defaultNPostconditionForContextSpecCases;
        } else if (visibility == Constants.ACC_PRIVATE) {
            return AspectUtil.getInstance().privateNPostconditionForContextSpecCases;
        } else {
            return AspectUtil.getInstance().nPostconditionForContextSpecCases;
        }
    }

    protected HashMap getContextForXPost(long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            return AspectUtil.getInstance().publicXPostconditionForContextSpecCases;
        } else if (visibility == Constants.ACC_PROTECTED) {
            return AspectUtil.getInstance().protectedXPostconditionForContextSpecCases;
        } else if (visibility == 0L) { //default
            return AspectUtil.getInstance().defaultXPostconditionForContextSpecCases;
        } else if (visibility == Constants.ACC_PRIVATE) {
            return AspectUtil.getInstance().privateXPostconditionForContextSpecCases;
        } else {
            return AspectUtil.getInstance().xPostconditionForContextSpecCases;
        }
    }

    protected HashMap getTokenReferenceForNPost(long visibility) {
        if (visibility == Constants.ACC_PUBLIC) {
            return AspectUtil.getInstance().publicNPostTokenReferenceSpecCases;
        } else if (visibility == Constants.ACC_PROTECTED) {
            return AspectUtil.getInstance().protectedNPostTokenReferenceSpecCases;
        } else if (visibility == 0L) { //default
            return AspectUtil.getInstance().defaultNPostTokenReferenceSpecCases;
        } else if (visibility == Constants.ACC_PRIVATE) {
            return AspectUtil.getInstance().privateNPostTokenReferenceSpecCases;
        } else {
            return AspectUtil.getInstance().nPostTokenReferenceSpecCases;
        }
    }

//	protected HashMap getTokenReferenceForXPost(long visibility){
//		if (visibility == Constants.ACC_PUBLIC) {
//			return AspectUtil.getInstance().publicXPostTokenReferenceSpecCases;
//		} else if (visibility == Constants.ACC_PROTECTED) {
//			return AspectUtil.getInstance().protectedXPostTokenReferenceSpecCases;
//		} else if (visibility == 0L) { //default
//			return AspectUtil.getInstance().defaultXPostTokenReferenceSpecCases;
//		} else if (visibility == Constants.ACC_PRIVATE) {
//			return AspectUtil.getInstance().privateXPostTokenReferenceSpecCases;
//		}
//		else{
//			return AspectUtil.getInstance().xPostTokenReferenceSpecCases;
//		}
//	}

    protected String buildCallProceed(JFormalParameter[] parameters, String instrumentationType, /*boolean isInnerType,*/ final boolean isMethodCrosscutSpecChecking, boolean isFlexibleXCS) {
        final StringBuffer code = new StringBuffer();
        code.append("proceed");

        // formal parameters
        code.append("(");
        if ((!isStatic) && (!isFlexibleXCS)) {
            if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                if (!this.methodDecl.isConstructor()) {
                    code.append("object$rac");
                }
            } else {
                code.append("object$rac");
            }
        }
        if (parameters != null) {
            if (parameters.length > 0)
                if (!isStatic) {
                    if (instrumentationType.equals("callSite") || instrumentationType.equals("clientAwareChecking")) {
                        if (!this.methodDecl.isConstructor()) {
                            if (parameters.length == 1) {
                                if (!TransUtils.toString(parameters[0].getType()).equals("org.aspectj.lang.JoinPoint")) {
                                    code.append(", ");
                                }
                            } else {
                                code.append(", ");
                            }
                        }
                    } else {
                        if (isMethodCrosscutSpecChecking) {
                            if (parameters.length == 1) {
                                if (!TransUtils.toString(parameters[0].getType()).equals("org.aspectj.lang.JoinPoint")) {
                                    code.append(", ");
                                }
                            } else {
                                code.append(", ");
                            }
                        } else {
                            code.append(", ");
                        }
                    }
                }
            for (int i = 0; i < parameters.length; i++) {
                if (i != 0)
                    code.append(", ");

                parameters[i].accept(new JmlAbstractVisitor() {
                    public void visitJmlFormalParameter(
                            JmlFormalParameter self) {
                        String ident = self.ident();
                        if (isMethodCrosscutSpecChecking) {
                            if (!(AspectUtil.replaceDollaSymbol(TransUtils.toString(self.getType())).equals("org.aspectj.lang.JoinPoint"))) {
                                code.append(ident);
                            }
                        } else {
                            code.append(ident);
                        }
                    }
                });
            }
        }
//		}

        code.append(")");

        return code.toString();
    }

    protected String xPostRethrowStmt(List<CType> exceptionsInSignalsClauses) {
        final StringBuffer rethrowStmt = new StringBuffer("");
//		CClassType exceptions[] = this.methodDecl.getExceptions();

        // build exception rethrow statements to be executed if the 
        // exceptional condition be satisfied

        if (!Main.aRacOptions.multipleSpecCaseChecking()) {
            rethrowStmt.append("         if(!JMLChecker.hasAnyJMLError) {\n");
            rethrowStmt.append("\t\t\t JMLChecker.rethrowUncheckedException(rac$e);\n");
            rethrowStmt.append("\t\t   }\n");
        } else {
            rethrowStmt.append("         JMLChecker.rethrowUncheckedException(rac$e);\n");
        }

        if (exceptionsInSignalsClauses.size() > 0) {
            for (Iterator<CType> iterator = exceptionsInSignalsClauses.iterator(); iterator
                    .hasNext(); ) {
                CType cType = iterator.next();
                if ((!cType.toString().startsWith("java.lang"))) {
                    rethrowStmt.append("\t\t\t if (" + VN_EXCEPTION);
                    rethrowStmt.append(" instanceof ").append(cType.toString().replace("$", ".")).append(") {\n");
                    if (Main.aRacOptions.multipleSpecCaseChecking()) {
                        rethrowStmt.append("\t\t\t   JMLChecker.resetXPostconditionError();\n");
                    }
                    rethrowStmt.append("\t\t\t   throw new JMLInternalRuntimeException((" + cType.toString().replace("$", ".") + ")" + VN_EXCEPTION + ");\n");
                    rethrowStmt.append("\t\t\t }\n");
                }
            }
        }

        return rethrowStmt.toString();
    }

    protected String xPostRethrowStmt() {
        final StringBuffer rethrowStmt = new StringBuffer("");
        CClassType exceptions[] = this.methodDecl.getExceptions();

        // build exception rethrow statements to be executed if the 
        // exceptional condition be satisfied

        if (!Main.aRacOptions.multipleSpecCaseChecking()) {
            rethrowStmt.append("         if(!JMLChecker.hasAnyJMLError) {\n");
            rethrowStmt.append("\t\t\t JMLChecker.rethrowUncheckedException(rac$e);\n");
            rethrowStmt.append("\t\t   }\n");
        } else {
            rethrowStmt.append("         JMLChecker.rethrowUncheckedException(rac$e);\n");
        }

        if (exceptions.length > 0) {
            for (int i = 0; i < exceptions.length; i++) {
                CClassType cType = exceptions[i];
                // complementing exception signals set --- [[[hemr]]]
                AspectUtil.getInstance().appendExceptionInSignalsClauseInCompilationUnit(cType);
                if ((!cType.toString().startsWith("java.lang"))) {
                    rethrowStmt.append("\t\t\t if (" + VN_EXCEPTION);
                    rethrowStmt.append(" instanceof ").append(cType.toString().replace("$", ".")).append(") {\n");
                    if (Main.aRacOptions.multipleSpecCaseChecking()) {
                        rethrowStmt.append("\t\t\t   JMLChecker.resetXPostconditionError();\n");
                    }
                    rethrowStmt.append("\t\t\t   throw new JMLInternalRuntimeException((" + cType.toString().replace("$", ".") + ")" + VN_EXCEPTION + ");\n");
                    rethrowStmt.append("\t\t\t }\n");
                }
            }
        }

        return rethrowStmt.toString();
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /**
     * target method for which assertion method is generated
     */
    protected final JmlMethodDeclaration methodDecl;

    /**
     * parameters of the target method
     */
    protected final JFormalParameter[] parameters;

    /**
     * name of the target method
     */
    protected String name;
}

