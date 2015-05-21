/*
 *
 * This file is part of JML
 * Copyright (C) 2008, 2009 Federal University of Pernambuco
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
 * $Id: TransMethod.java,v 1.23 2008/07/19 10:51:36 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jmlspecs.checker.JmlAbstractVisitor;
import org.jmlspecs.checker.JmlAssignableClause;
import org.jmlspecs.checker.JmlBehaviorSpec;
import org.jmlspecs.checker.JmlEnsuresClause;
import org.jmlspecs.checker.JmlExceptionalBehaviorSpec;
import org.jmlspecs.checker.JmlExtendingSpecification;
import org.jmlspecs.checker.JmlForAllVarDecl;
import org.jmlspecs.checker.JmlFormalParameter;
import org.jmlspecs.checker.JmlGeneralSpecCase;
import org.jmlspecs.checker.JmlGenericSpecCase;
import org.jmlspecs.checker.JmlLetVarDecl;
import org.jmlspecs.checker.JmlMessages;
import org.jmlspecs.checker.JmlMethodDeclaration;
import org.jmlspecs.checker.JmlMethodSpecification;
import org.jmlspecs.checker.JmlNormalBehaviorSpec;
import org.jmlspecs.checker.JmlPredicate;
import org.jmlspecs.checker.JmlPredicateClause;
import org.jmlspecs.checker.JmlRequiresClause;
import org.jmlspecs.checker.JmlResultExpression;
import org.jmlspecs.checker.JmlSignalsClause;
import org.jmlspecs.checker.JmlSignalsOnlyClause;
import org.jmlspecs.checker.JmlSourceField;
import org.jmlspecs.checker.JmlSpecBodyClause;
import org.jmlspecs.checker.JmlSpecCase;
import org.jmlspecs.checker.JmlSpecExpression;
import org.jmlspecs.checker.JmlSpecVarDecl;
import org.jmlspecs.checker.JmlSpecification;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.checker.JmlVariableDefinition;
import org.jmlspecs.checker.JmlVisitor;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.CBinaryField;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CType;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JConditionalOrExpression;
import org.multijava.mjc.JEqualityExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.util.compiler.TokenReference;

/**
 * A class for translating JML annotated Java methods into RAC-enabled
 * methods. The translation produces new methods and fields that must
 * be added to the target class, and also renames the original method.
 * <p/>
 * <p> A <code>non_null</code> annotation to a formal parameter is
 * interpreted as a part of preconditions. That is, a
 * <code>non_null</code> annotation to a formal parameter, say
 * <code>x</code>, has the same effect as conjoining the predicate
 * <code>x != null</code> to the precondition of the method.  </p>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.68 $
 */

//!FIXME! replace rac$e and rac$b with constants!

public class TransMethod extends TransUtils {

    /** True if we are generating a test wrapper for a spec file (and we do 
     not have the original source).
     */
    // protected boolean genSpecTestFile = false;

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a new <code>TransMethod</code> object.
     *
     * @param typeDecl target type declaration whose methods are to be
     *                 translated.
     * @param varGen   variable name generator
     *                 <p/>
     *                 <pre><jml>
     *                                                                                                                                   requires typeDecl != null && varGen != null;
     *                                                                                                                                 </jml></pre>
     */
    public TransMethod(JmlTypeDeclaration typeDecl, VarGenerator varGen) {
        this.typeDecl = typeDecl;
        this.varGen = varGen;
        this.newMethods = new ArrayList();
        this.newFields = new ArrayList();
    }

    // ----------------------------------------------------------------------
    // ACCESSOR METHODS
    // ----------------------------------------------------------------------

    /**
     * Returns true if any new field declarations has been generated
     * as the result of translation.
     * <p/>
     * <pre><jml>
     * ensures  \result == newFields.size() > 0;
     * </jml></pre>
     */
    public boolean hasNewFields() {
        return newFields.size() > 0;
    }

    /**
     * Returns true if any new method declarations has been generated
     * as the result of translation.
     * <p/>
     * <pre><jml>
     * ensures  \result == newMethods.size() > 0;
     * </jml></pre>
     */
    public boolean hasNewMethods() {
        return newMethods.size() > 0;
    }

    /**
     * Returns a list of new field declarations created by this
     * translation, which need be added to the target class or interface.
     * <p/>
     * <pre><jml>
     * ensures  \result != null && (\forall Object o; \result.contains(o);
     *   (o instanceof String) &&
     *   (* o has the form: "[static] T v = init;\n" *));
     * </jml></pre>
     */
    public List newFields() {
        return newFields;
    }

    /**
     * Returns a list of new method declaratons created by this
     * transformation, and need be added to the target class or instance.
     * <p/>
     * <pre><jml>
     * ensures  \result != null && (\forall Object o; \result.contains(o);
     *   (o instanceof JmlMethodDeclaration));
     * </jml></pre>
     */
    public List newMethods() {
        return newMethods;
    }

    // ----------------------------------------------------------------------
    // TRANSLATION
    // ----------------------------------------------------------------------

    /**
     * Peforms translation leaving the results in appropriate instance
     * variables.
     *
     * @param methodDecl method to translate
     *                   <p/>
     *                   <pre><jml>
     *                                                                                                                                                                                                                                                                               requires methodDecl != null && typeDecl.methods().contains(methodDecl);
     *                                                                                                                                                                                                                                                                               assignable newMethods, newFields, this.methodDecl, desugaredSpec;
     *                                                                                                                                                                                                                                                                               assignable stackVar;
     *                                                                                                                                                                                                                                                                               </jml></pre>
     */
    public void perform(JmlMethodDeclaration methodDecl) {
        this.methodDecl = methodDecl;

        // desugar method specification 
        if (methodDecl.hasSpecification()) {
            DesugarSpec desugar = new DesugarSpec();
            desugaredSpec =
                    desugar.perform(methodDecl.methodSpecification(),
                            methodDecl.getExceptions());
        }
        // generate assertion check methods such as pre and postcondition
        // check methods.
        //PreValueVars vars = genAssertionMethods();
        genAssertionMethods();

        // This method must be called last because it produces some
        // side-effects, e.g., making it a private internal method.
        //genWrapperMethod();
    }

    /**
     * Generates pre/postcondition check methods. The generated
     * methods and any fields (generated as side-effects) are added to
     * the instance fields <code>newMethods</code> and
     * <code>newFields</code> respectively. Returned is the set of
     * (generated) private fields that need to be saved before, and
     * restored after the execution of the method body, due to
     * the possiblity of recursive method calls.
     * <p/>
     * <pre><jml>
     * requires (* desugaredSpec has desugared method spec *);
     * //assignable newMethods, newFields, stackVar;
     * ensures \result != null;
     * </jml></pre>
     */
    protected PreValueVars genAssertionMethods() {
        // fresh variable generators
        VarGenerator preVarGen = VarGenerator.forMethod(varGen);
        VarGenerator postVarGen = VarGenerator.forMethod(varGen);

        // translation result accumulators
        RacNode preStmt = null;
        RacNode postStmt = null;

        List epostCode = new ArrayList();
        List publicEpostCode = new ArrayList();
        List protectedEpostCode = new ArrayList();
        List defaultEpostCode = new ArrayList();
        List privateEpostCode = new ArrayList();

        // translation result assertions
        StringBuffer precondition = new StringBuffer();
        StringBuffer nPostcondition = new StringBuffer();
        JmlSignalsClause[] xPostcondition = null;

        // translation result assertions for visibility specs
        StringBuffer publicPrecondition = new StringBuffer();
        StringBuffer publicNPostcondition = new StringBuffer();
        StringBuffer protectedPrecondition = new StringBuffer();
        StringBuffer protectedNPostcondition = new StringBuffer();
        StringBuffer defaultPrecondition = new StringBuffer();
        StringBuffer defaultNPostcondition = new StringBuffer();
        StringBuffer privatePrecondition = new StringBuffer();
        StringBuffer privateNPostcondition = new StringBuffer();

        // context information
        StringBuffer nPostconditionForContext = new StringBuffer();
        StringBuffer xPostconditionForContext = new StringBuffer();

        // context information of visibility specs
        StringBuffer publicNPostconditionForContext = new StringBuffer();
        StringBuffer publicXPostconditionForContext = new StringBuffer();
        StringBuffer protectedNPostconditionForContext = new StringBuffer();
        StringBuffer protectedXPostconditionForContext = new StringBuffer();
        StringBuffer defaultNPostconditionForContext = new StringBuffer();
        StringBuffer defaultXPostconditionForContext = new StringBuffer();
        StringBuffer privateNPostconditionForContext = new StringBuffer();
        StringBuffer privateXPostconditionForContext = new StringBuffer();

        // predicate token references at specs
        StringBuffer preTokenReference = new StringBuffer();

        // predicate token references at specs for visibility specs
        StringBuffer publicPreTokenReference = new StringBuffer();
        StringBuffer protectedPreTokenReference = new StringBuffer();
        StringBuffer defaultPreTokenReference = new StringBuffer();
        StringBuffer privatePreTokenReference = new StringBuffer();

        // for AspectJML/XCS --- [[[hemr]]]
        exceptionsInSignalsClauses = new ArrayList<CType>();

        // A list of RacNode corresponding to old expressions found in
        // normal and exceptional postconditions of this method
        // specification, collected to evaluate them in the pre-state
        // and store the results to the corresponding, generated
        // private fields. The declaration of the private field (of
        // the type PreValueVars.Entry) is piggybacked through the
        // varDecl field of the RacNode.		
        HashMap oldVarsDecl = new HashMap();
        HashMap publicOldVarsDecl = new HashMap();
        HashMap protectedOldVarsDecl = new HashMap();
        HashMap defaultOldVarsDecl = new HashMap();
        HashMap privateOldVarsDecl = new HashMap();

        HashMap oldExprs = new HashMap();
        HashMap publicOldExprs = new HashMap();
        HashMap protectedOldExprs = new HashMap();
        HashMap defaultOldExprs = new HashMap();
        HashMap privateOldExprs = new HashMap();

        HashMap oldExprsDecl = new HashMap();
        HashMap publicOldExprsDecl = new HashMap();
        HashMap protectedOldExprsDecl = new HashMap();
        HashMap defaultOldExprsDecl = new HashMap();
        HashMap privateOldExprsDecl = new HashMap();

        List preExprs = new ArrayList();
        List publicPreExprs = new ArrayList();
        List protectedPreExprs = new ArrayList();
        List defaultPreExprs = new ArrayList();
        List privatePreExprs = new ArrayList();

        List preExprsDecl = new ArrayList();
        List publicPreExprsDecl = new ArrayList();
        List protectedPreExprsDecl = new ArrayList();
        List defaultPreExprsDecl = new ArrayList();
        List privatePreExprsDecl = new ArrayList();

        // expression to check non_null annotations of parameters and result.
        JExpression preNonNullExpr = null;
        JExpression postNonNullExpr = null;

        // expression to check if the current method has postconditions.
        boolean hasPrecondition = false;
        boolean hasPublicPrecondition = false;
        boolean hasProtectedPrecondition = false;
        boolean hasDefaultPrecondition = false;
        boolean hasPrivatePrecondition = false;

        // verify if the current method also has non_null annotations
        preNonNullExpr = preNonNullAnnotations();
        postNonNullExpr = postNonNullAnnotation();

        AspectUtil.getInstance().initializeMethodSpecCaseCheckingContent();
        boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);

        boolean isEmptySpecCaseWithNonNullPre = false;

        // reseting this field for later test related to XCS --- [[[hemr]]]
        if (isMethodCrosscutSpecChecking) {
            AspectUtil.getInstance().hasThisRef = false;
            AspectUtil.getInstance().isStaticPC = false;
        }

        // if the current method has explicit spec cases
        if (methodHasRealExplicitSpecs()) {
            RacContext ctx = RacContext.createPositive();
            TransExpression2 transPre = null;
            String transPreStr = "true"; // default to true due to the \same predicate --- [[[hemr]]]
            TransPostExpression2 transNPost = null;
            long visibility;

            // Spec cases of a method declaration
            SpecCaseCollector specs = new SpecCaseCollector(desugaredSpec);
            int preVarCount = 0;
            int preExprsDeclCount = 0;
            int publicPreExprsDeclCount = 0;
            int protectedPreExprsDeclCount = 0;
            int defaultPreExprsDeclCount = 0;
            int privatePreExprsDeclCount = 0;

            // validating spec cases visibility with meth visibility.
            // this is an important issue of information hiding.
            // if a method has heavyweight spec cases, one of them should have
            // the same visibility as the method --- [[[hemr]]]
            visibility = this.privacy(this.methodDecl.modifiers());
            if (!this.isValidSpecCases(visibility, methodDecl.methodSpecification().specCases())) {
                JmlRacGenerator.fail(this.methodDecl.getTokenReference(), JmlMessages.INVALID_METHOD_SPEC_CASES, this.methodDecl.ident());
            }

            int index = 0;
            Iterator iter = specs.iterator();
            while (iter.hasNext()) {
                SpecCase c = (SpecCase) iter.next();
                visibility = extractVisibilitySpecs(preVarCount);
                // translate spec vars if any
                if (c.hasSpecVarDecls()) {
                    List oldVars = translateSpecVarDecls(c.specVarDecls(), preVarGen);
                    if (Main.aRacOptions.callSiteInstrumentation() || Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            publicOldVarsDecl.put(index, oldVars);
                        } else if (visibility == ACC_PROTECTED) {
                            protectedOldVarsDecl.put(index, oldVars);
                        } else if (visibility == 0L) {
                            defaultOldVarsDecl.put(index, oldVars);
                        } else if (visibility == ACC_PRIVATE) {
                            privateOldVarsDecl.put(index, oldVars);
                        }
                    }
                    oldVarsDecl.put(index, oldVars);
                }

                // translate precondition if exists; (henrique rebelo)
                JExpression pred = c.precondition();
                if (!isMethodCrosscutSpecChecking) {
                    if (preNonNullExpr != null) {
                        // make non_null annotations a part of precondition
                        if (pred instanceof RacPredicate) {
                            if (!((RacPredicate) pred).isTrueLiteral())
                                ((RacPredicate) pred).countCoverage();
                        }
                        if (preNonNullExpr instanceof RacPredicate) {
                            ((RacPredicate) preNonNullExpr).countCoverage();
                        }
                        pred = pred == null ? preNonNullExpr :
                                new JConditionalAndExpression(pred.getTokenReference(),
                                        preNonNullExpr, pred);
                        AspectUtil.getInstance().appendDefaultRequiresClauseTokenRefereces(preNonNullExpr.getTokenReference().toString());
                    }
                }
                // if the spec cases have preconditions
                if (c.hasPrecondition() && pred != null) {
                    hasPrecondition = true;
                    transPre = new TransExpression2(preVarGen, ctx, pred, null, typeDecl, "JMLEntryPreconditionError");
                    preStmt = RacParser.parseStatement("", preStmt, transPre.stmt(true));

                    transPreStr = transPre.stmtAsString();
                    // verifying if the advice generation will need to handle this/target exposure due to "this." references in JML specs --- [[[hemr]]]
                    if (isMethodCrosscutSpecChecking) {
                        if (transPreStr.contains("this.")) {
                            AspectUtil.getInstance().hasThisRef = true;
                        }
                    }

                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            hasPublicPrecondition = true;
                            this.combineSpecCasesForPrecondition(publicPrecondition, transPreStr);
                            this.combineTokenReferenceForPred(publicPreTokenReference, transPre.getTokenReference());
                        } else if (visibility == ACC_PROTECTED) {
                            hasProtectedPrecondition = true;
                            this.combineSpecCasesForPrecondition(protectedPrecondition, transPreStr);
                            this.combineTokenReferenceForPred(protectedPreTokenReference, transPre.getTokenReference());
                        } else if (visibility == 0L) {
                            hasDefaultPrecondition = true;
                            this.combineSpecCasesForPrecondition(defaultPrecondition, transPreStr);
                            this.combineTokenReferenceForPred(defaultPreTokenReference, transPre.getTokenReference());
                        } else if (visibility == ACC_PRIVATE) {
                            hasPrivatePrecondition = true;
                            this.combineSpecCasesForPrecondition(privatePrecondition, transPreStr);
                            this.combineTokenReferenceForPred(privatePreTokenReference, transPre.getTokenReference());
                        }
                    }
                    this.combineSpecCasesForPrecondition(precondition, transPreStr);
                    this.combineTokenReferenceForPred(preTokenReference, transPre.getTokenReference());

                    // updating hashmap related to spec-cases
                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            AspectUtil.getInstance().publicPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                        } else if (visibility == ACC_PROTECTED) {
                            AspectUtil.getInstance().protectedPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                        } else if (visibility == 0L) {
                            AspectUtil.getInstance().defaultPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                        } else if (visibility == ACC_PRIVATE) {
                            AspectUtil.getInstance().privatePreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                        }
                    }
                    AspectUtil.getInstance().preconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                }

                // translate postcondition if exists; (henrique rebelo)
                pred = c.postcondition();
                if (postNonNullExpr != null) {
                    // make non_null annotations a part of normal postcondition
                    if (pred instanceof RacPredicate) {
                        if (!((RacPredicate) pred).isTrueLiteral()) {
                            ((RacPredicate) pred).countCoverage();
                        }
                    }
                    if (postNonNullExpr instanceof RacPredicate) {
                        ((RacPredicate) postNonNullExpr).countCoverage();
                    }
                    pred = pred == null ? postNonNullExpr :
                            new JConditionalAndExpression(pred.getTokenReference(),
                                    postNonNullExpr, pred);
                    AspectUtil.getInstance().appendDefaultEnsuresClauseTokenRefereces(postNonNullExpr.getTokenReference().toString());
                }
                // if the spec cases have postconditions
                if (c.hasPostcondition()) {
                    transNPost = new TransPostExpression2(
                            postVarGen, ctx, preVarGen, methodDecl.isStatic(),
                            pred, null, typeDecl, "JMLExitNormalPostconditionError");
                    RacNode stmt = transNPost.stmt(true);
                    postStmt = RacParser.parseStatement("", postStmt, stmt);

                    // verifying if the advice generation will need to handle this/target exposure due to "this." references in JML specs --- [[[hemr]]]
                    if (isMethodCrosscutSpecChecking) {
                        if (transNPost.stmtAsString().contains("this.")) {
                            AspectUtil.getInstance().hasThisRef = true;
                        }
                    }

                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            this.combineSpecCases(publicNPostconditionForContext, transNPost.stmtAsString());
                            AspectUtil.getInstance().publicNPostconditionForContextSpecCases.put(index, this.getContextValues(transNPost.stmtAsString()));
                            AspectUtil.getInstance().publicNPostTokenReferenceSpecCases.put(index, transNPost.getTokenReference());
                        } else if (visibility == ACC_PROTECTED) {
                            this.combineSpecCases(protectedNPostconditionForContext, transNPost.stmtAsString());
                            AspectUtil.getInstance().protectedNPostconditionForContextSpecCases.put(index, this.getContextValues(transNPost.stmtAsString()));
                            AspectUtil.getInstance().protectedNPostTokenReferenceSpecCases.put(index, transNPost.getTokenReference());
                        } else if (visibility == 0L) {
                            this.combineSpecCases(defaultNPostconditionForContext, transNPost.stmtAsString());
                            AspectUtil.getInstance().defaultNPostconditionForContextSpecCases.put(index, this.getContextValues(transNPost.stmtAsString()));
                            AspectUtil.getInstance().defaultNPostTokenReferenceSpecCases.put(index, transNPost.getTokenReference());
                        } else if (visibility == ACC_PRIVATE) {
                            this.combineSpecCases(privateNPostconditionForContext, transNPost.stmtAsString());
                            AspectUtil.getInstance().privateNPostconditionForContextSpecCases.put(index, this.getContextValues(transNPost.stmtAsString()));
                            AspectUtil.getInstance().privateNPostTokenReferenceSpecCases.put(index, transNPost.getTokenReference());
                        }
                    }
                    this.combineSpecCases(nPostconditionForContext, transNPost.stmtAsString());
                    AspectUtil.getInstance().nPostconditionForContextSpecCases.put(index, this.getContextValues(transNPost.stmtAsString()));
                    AspectUtil.getInstance().nPostTokenReferenceSpecCases.put(index, transNPost.getTokenReference());

                    if (this.hasFieldReferenceInPrecondition(transPreStr) || this.hasMethodCallExpInPrecondition(transPreStr)) {
                        String var = "rac$pre" + preExprsDeclCount;
                        preExprsDecl.add(var);
                        String varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                        preExprs.add(varAssign);
                        preExprsDeclCount++;
                        if (Main.aRacOptions.clientAwareChecking()) {
                            //verifying visibility for translation and composition (combination of spec cases)
                            if (visibility == ACC_PUBLIC) {
                                var = "rac$pre" + publicPreExprsDeclCount;
                                varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                                publicPreExprsDecl.add(var);
                                publicPreExprs.add(varAssign);
                                this.combineSpecCases(publicNPostcondition, this.combinePreAndNPost(var, transNPost.stmtAsString()));
                                publicPreExprsDeclCount++;
                                AspectUtil.getInstance().publicPreconditionSpecCases.put(index, var);
                                AspectUtil.getInstance().publicNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (visibility == ACC_PROTECTED) {
                                var = "rac$pre" + protectedPreExprsDeclCount;
                                varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                                protectedPreExprsDecl.add(var);
                                protectedPreExprs.add(varAssign);
                                this.combineSpecCases(protectedNPostcondition, this.combinePreAndNPost(var, transNPost.stmtAsString()));
                                protectedPreExprsDeclCount++;
                                AspectUtil.getInstance().protectedPreconditionSpecCases.put(index, var);
                                AspectUtil.getInstance().protectedNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (visibility == 0L) {
                                var = "rac$pre" + defaultPreExprsDeclCount;
                                varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                                defaultPreExprsDecl.add(var);
                                defaultPreExprs.add(varAssign);
                                this.combineSpecCases(defaultNPostcondition, this.combinePreAndNPost(var, transNPost.stmtAsString()));
                                defaultPreExprsDeclCount++;
                                AspectUtil.getInstance().defaultPreconditionSpecCases.put(index, var);
                                AspectUtil.getInstance().defaultNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (visibility == ACC_PRIVATE) {
                                var = "rac$pre" + privatePreExprsDeclCount;
                                varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                                privatePreExprsDecl.add(var);
                                privatePreExprs.add(varAssign);
                                this.combineSpecCases(privateNPostcondition, this.combinePreAndNPost(var, transNPost.stmtAsString()));
                                privatePreExprsDeclCount++;
                                AspectUtil.getInstance().privatePreconditionSpecCases.put(index, var);
                                AspectUtil.getInstance().privateNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            }
                        }
                        this.combineSpecCases(nPostcondition, this.combinePreAndNPost(var, transNPost.stmtAsString()));
                        AspectUtil.getInstance().preconditionSpecCases.put(index, var);
                        AspectUtil.getInstance().nPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                    } else {
                        if (!transNPost.stmtAsString().equals("true")) {
                            //Eliminating redundancy
                            if (nPostcondition.toString().equals("true")) {
                                nPostcondition = new StringBuffer();
                            }

                            if (Main.aRacOptions.clientAwareChecking()) {
                                //verifying visibility for translation and composition (combination of spec cases)
                                if (visibility == ACC_PUBLIC) {
                                    this.combineSpecCases(publicNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                    AspectUtil.getInstance().publicPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                    AspectUtil.getInstance().publicNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                                } else if (visibility == ACC_PROTECTED) {
                                    this.combineSpecCases(protectedNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                    AspectUtil.getInstance().protectedPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                    AspectUtil.getInstance().protectedNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                                } else if (visibility == 0L) {
                                    this.combineSpecCases(defaultNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                    AspectUtil.getInstance().defaultPreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                    AspectUtil.getInstance().defaultNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                                } else if (visibility == ACC_PRIVATE) {
                                    this.combineSpecCases(privateNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                    AspectUtil.getInstance().privatePreconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                    AspectUtil.getInstance().privateNPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                                }
                            }
                            this.combineSpecCases(nPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                            AspectUtil.getInstance().preconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                            AspectUtil.getInstance().nPostconditionSpecCases.put(index, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                        }
                    }

                    // list of old expressions
                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            publicOldExprs.put(index, transNPost.oldExprs());
                            publicOldExprsDecl.put(index, transNPost.oldVarDecl());
                        } else if (visibility == ACC_PROTECTED) {
                            protectedOldExprs.put(index, transNPost.oldExprs());
                            protectedOldExprsDecl.put(index, transNPost.oldVarDecl());
                        } else if (visibility == 0L) { //default
                            defaultOldExprs.put(index, transNPost.oldExprs());
                            defaultOldExprsDecl.put(index, transNPost.oldVarDecl());
                        } else if (visibility == ACC_PRIVATE) {
                            privateOldExprs.put(index, transNPost.oldExprs());
                            privateOldExprsDecl.put(index, transNPost.oldVarDecl());
                        }
                    }
                    oldExprs.put(index, transNPost.oldExprs());
                    oldExprsDecl.put(index, transNPost.oldVarDecl());
                } else if (nPostcondition.length() <= 0) {
                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            publicNPostcondition.append("true");
                            AspectUtil.getInstance().publicNPostconditionSpecCases.put(index, "true");
                        } else if (visibility == ACC_PROTECTED) {
                            protectedNPostcondition.append("true");
                            AspectUtil.getInstance().protectedNPostconditionSpecCases.put(index, "true");
                        } else if (visibility == 0L) {
                            defaultNPostcondition.append("true");
                            AspectUtil.getInstance().defaultNPostconditionSpecCases.put(index, "true");
                        } else if (visibility == ACC_PRIVATE) {
                            privateNPostcondition.append("true");
                            AspectUtil.getInstance().privateNPostconditionSpecCases.put(index, "true");
                        }
                    }
                    nPostcondition.append("true");
                    AspectUtil.getInstance().nPostconditionSpecCases.put(index, "true");
                }

                // translate exceptional postcondition if exists; (henrique rebelo)
                if (c.hasExceptionalPostcondition()) {
                    xPostcondition = c.exceptionalPostcondition();
                    if (this.hasFieldReferenceInPrecondition(transPreStr) || this.hasMethodCallExpInPrecondition(transPreStr)) {
                        if (c.hasPostcondition()) {
                            if (Main.aRacOptions.clientAwareChecking()) {
                                //verifying visibility for translation and composition (combination of spec cases)
                                if (visibility == ACC_PUBLIC) {
                                    publicEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) publicPreExprsDecl.get(publicPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == ACC_PROTECTED) {
                                    protectedEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) protectedPreExprsDecl.get(protectedPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == 0L) {
                                    defaultEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) defaultPreExprsDecl.get(defaultPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == ACC_PRIVATE) {
                                    privateEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) privatePreExprsDecl.get(privatePreExprsDeclCount - 1)), typeDecl) + ") {");
                                }
                            }
                            epostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) preExprsDecl.get(preExprsDeclCount - 1)), typeDecl) + ") {");
                        } else {
                            String var = "rac$pre" + preExprsDeclCount;
                            preExprsDecl.add(var);
                            String varAssign = var + " = " + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl) + ";";
                            preExprs.add(varAssign);
                            preExprsDeclCount++;

                            epostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) preExprsDecl.get(preExprsDeclCount - 1)), typeDecl) + ") {");

                            if (Main.aRacOptions.clientAwareChecking()) {
                                //verifying visibility for translation and composition (combination of spec cases)
                                if (visibility == ACC_PUBLIC) {
                                    var = "rac$pre" + publicPreExprsDeclCount;
                                    publicPreExprsDecl.add(var);
                                    publicPreExprs.add(varAssign);
                                    publicPreExprsDeclCount++;
                                    publicEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) publicPreExprsDecl.get(publicPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == ACC_PROTECTED) {
                                    var = "rac$pre" + protectedPreExprsDeclCount;
                                    protectedPreExprsDecl.add(var);
                                    protectedPreExprs.add(varAssign);
                                    protectedPreExprsDeclCount++;
                                    protectedEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) protectedPreExprsDecl.get(protectedPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == 0L) {
                                    var = "rac$pre" + defaultPreExprsDeclCount;
                                    defaultPreExprsDecl.add(var);
                                    defaultPreExprs.add(varAssign);
                                    defaultPreExprsDeclCount++;
                                    defaultEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) defaultPreExprsDecl.get(defaultPreExprsDeclCount - 1)), typeDecl) + ") {");
                                } else if (visibility == ACC_PRIVATE) {
                                    var = "rac$pre" + privatePreExprsDeclCount;
                                    privatePreExprsDecl.add(var);
                                    privatePreExprs.add(varAssign);
                                    privatePreExprsDeclCount++;
                                    privateEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(((String) privatePreExprsDecl.get(privatePreExprsDeclCount - 1)), typeDecl) + ") {");
                                }
                            }
                        }
                    } else {
                        if (Main.aRacOptions.clientAwareChecking()) {
                            //verifying visibility for translation and composition (combination of spec cases)
                            if (visibility == ACC_PUBLIC) {
                                publicEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, typeDecl) + ") {");
                            } else if (visibility == ACC_PROTECTED) {
                                protectedEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, typeDecl) + ") {");
                            } else if (visibility == 0L) {
                                defaultEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, typeDecl) + ") {");
                            } else if (visibility == ACC_PRIVATE) {
                                privateEpostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, typeDecl) + ") {");
                            }
                        }
                        epostCode.add("\n\t\t   if (" + AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, typeDecl) + ") {");
                    }

                    for (int i = 0; i < xPostcondition.length; i++) {
                        if (xPostcondition[i].hasPredicate() && !xPostcondition[i].isNotSpecified()) {
                            String currentEpostTranslated = translateSignalsClause(
                                    postVarGen,
                                    preVarGen,
                                    xPostcondition[i],
                                    xPostconditionForContext,
                                    AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl),
                                    index,
                                    oldExprs,
                                    oldExprsDecl);
                            epostCode.add(currentEpostTranslated);

                            if (Main.aRacOptions.clientAwareChecking()) {
                                //verifying visibility for translation and composition (combination of spec cases)
                                if (visibility == ACC_PUBLIC) {
                                    currentEpostTranslated = translateSignalsClause(
                                            postVarGen,
                                            preVarGen,
                                            xPostcondition[i],
                                            publicXPostconditionForContext,
                                            AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl),
                                            index,
                                            publicOldExprs,
                                            publicOldExprsDecl);
                                    publicEpostCode.add(currentEpostTranslated);
                                } else if (visibility == ACC_PROTECTED) {
                                    currentEpostTranslated = translateSignalsClause(postVarGen,
                                            preVarGen, xPostcondition[i], protectedXPostconditionForContext, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl), index, protectedOldExprs, protectedOldExprsDecl);
                                    protectedEpostCode.add(currentEpostTranslated);
                                } else if (visibility == 0L) {
                                    currentEpostTranslated = translateSignalsClause(postVarGen,
                                            preVarGen, xPostcondition[i], defaultXPostconditionForContext, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl), index, defaultOldExprs, defaultOldExprsDecl);
                                    defaultEpostCode.add(currentEpostTranslated);
                                } else if (visibility == ACC_PRIVATE) {
                                    currentEpostTranslated = translateSignalsClause(postVarGen,
                                            preVarGen, xPostcondition[i], privateXPostconditionForContext, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl), index, privateOldExprs, privateOldExprsDecl);
                                    privateEpostCode.add(currentEpostTranslated);
                                }
                            }
                        }
                    }

                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (visibility == ACC_PUBLIC) {
                            publicEpostCode.add("\t\t   }");
                        } else if (visibility == ACC_PROTECTED) {
                            protectedEpostCode.add("\t\t   }");
                        } else if (visibility == 0L) {
                            defaultEpostCode.add("\t\t   }");
                        } else if (visibility == ACC_PRIVATE) {
                            privateEpostCode.add("\t\t   }");
                        }
                    }
                    epostCode.add("\t\t   }");
                }
                preVarCount++;
                index++;
            }
        }

        // if the current method does not have explicit spec cases
        else {
            TransExpression2 transPre = null;
            String transPreStr = null;
            if (!isMethodCrosscutSpecChecking) {
                if (preNonNullExpr != null) {
                    hasPrecondition = true;
                    isEmptySpecCaseWithNonNullPre = true;
                    if (preNonNullExpr instanceof RacPredicate)
                        ((RacPredicate) preNonNullExpr).countCoverage();

                    transPre = new TransExpression2(preVarGen, null, preNonNullExpr, null, typeDecl, "JMLEntryPreconditionError");
                    transPreStr = transPre.stmtAsString();
                    preStmt = RacParser.parseStatement("", transPre.stmt(true));

                    if (Main.aRacOptions.clientAwareChecking()) {
                        //verifying visibility for translation and composition (combination of spec cases)
                        if (methodDecl.getMethod().access().isPublic()) {
                            hasPublicPrecondition = true;
                            this.combineSpecCasesForPrecondition(publicPrecondition, transPreStr);
                        } else if (methodDecl.getMethod().access().isProtected()) {
                            hasProtectedPrecondition = true;
                            this.combineSpecCasesForPrecondition(protectedPrecondition, transPreStr);
                        } else if (methodDecl.getMethod().access().hasDefaultAccess()) {
                            hasDefaultPrecondition = true;
                            this.combineSpecCasesForPrecondition(defaultPrecondition, transPreStr);
                        } else if (methodDecl.getMethod().access().isPrivate()) {
                            hasPrivatePrecondition = true;
                            this.combineSpecCasesForPrecondition(privatePrecondition, transPreStr);
                        }
                    }
                    this.combineSpecCasesForPrecondition(precondition, transPreStr);
                }

                if (postNonNullExpr != null) {
                    TransPostExpression2 transNPost =
                            new TransPostExpression2(postVarGen, null, preVarGen,
                                    methodDecl.isStatic(),
                                    postNonNullExpr, null, typeDecl, "JMLExitNormalPostconditionError");
                    postStmt = RacParser.parseStatement("", transNPost.stmt(true));
                    if (transPre != null) {
                        if (Main.aRacOptions.clientAwareChecking()) {
                            //verifying visibility for translation and composition (combination of spec cases)
                            if (methodDecl.getMethod().access().isPublic()) {
                                this.combineSpecCases(publicNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                AspectUtil.getInstance().publicPreconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                AspectUtil.getInstance().publicNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().isProtected()) {
                                this.combineSpecCases(protectedNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                AspectUtil.getInstance().protectedPreconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                AspectUtil.getInstance().protectedNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().hasDefaultAccess()) {
                                this.combineSpecCases(defaultNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                AspectUtil.getInstance().defaultPreconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                AspectUtil.getInstance().defaultNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().isPrivate()) {
                                this.combineSpecCases(privateNPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                                AspectUtil.getInstance().privatePreconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                                AspectUtil.getInstance().privateNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            }
                        }
                        this.combineSpecCases(nPostcondition, this.combinePreAndNPost(transPreStr, transNPost.stmtAsString()));
                        AspectUtil.getInstance().preconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transPreStr, this.typeDecl));
                        AspectUtil.getInstance().nPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                    } else {
                        if (Main.aRacOptions.clientAwareChecking()) {
                            //verifying visibility for translation and composition (combination of spec cases)
                            if (methodDecl.getMethod().access().isPublic()) {
                                this.combineSpecCases(publicNPostcondition, this.combinePreAndNPost("true", transNPost.stmtAsString()));
                                AspectUtil.getInstance().publicPreconditionSpecCases.put(0, "true");
                                AspectUtil.getInstance().publicNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().isProtected()) {
                                this.combineSpecCases(protectedNPostcondition, this.combinePreAndNPost("true", transNPost.stmtAsString()));
                                AspectUtil.getInstance().protectedPreconditionSpecCases.put(0, "true");
                                AspectUtil.getInstance().protectedNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().hasDefaultAccess()) {
                                this.combineSpecCases(defaultNPostcondition, this.combinePreAndNPost("true", transNPost.stmtAsString()));
                                AspectUtil.getInstance().defaultPreconditionSpecCases.put(0, "true");
                                AspectUtil.getInstance().defaultNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            } else if (methodDecl.getMethod().access().isPrivate()) {
                                this.combineSpecCases(privateNPostcondition, this.combinePreAndNPost("true", transNPost.stmtAsString()));
                                AspectUtil.getInstance().privatePreconditionSpecCases.put(0, "true");
                                AspectUtil.getInstance().privateNPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                            }
                        }
                        this.combineSpecCases(nPostcondition, this.combinePreAndNPost("true", transNPost.stmtAsString()));
                        AspectUtil.getInstance().preconditionSpecCases.put(0, "true");
                        AspectUtil.getInstance().nPostconditionSpecCases.put(0, AspectUtil.changeThisOrSuperRefToAdviceRef(transNPost.stmtAsString(), this.typeDecl));
                    }
                }
            }

            // translate default exceptional postcondition; (henrique rebelo)
            DesugarSpec desugar = new DesugarSpec();
            JmlSignalsClause signals_clause = desugar.defaultSignalsClause2(this.methodDecl.getTokenReference(), this.methodDecl.getExceptions());

            if (signals_clause != null) {
                long visibility = this.privacy(this.methodDecl.modifiers());
                epostCode.add("\n\t\t   if (true) {");
                if (Main.aRacOptions.clientAwareChecking()) {
                    //verifying visibility for translation and composition (combination of spec cases)
                    if (visibility == ACC_PUBLIC) {
                        publicEpostCode.add("\n\t\t   if (true) {");
                    } else if (visibility == ACC_PROTECTED) {
                        protectedEpostCode.add("\n\t\t   if (true) {");
                    } else if (visibility == 0L) {
                        defaultEpostCode.add("\n\t\t   if (true) {");
                    } else if (visibility == ACC_PRIVATE) {
                        privateEpostCode.add("\n\t\t   if (true) {");
                    }
                }
                {
                    if (signals_clause.hasPredicate() && !signals_clause.isNotSpecified()) {
                        boolean isEqual = false;
                        for (Iterator iterator = AspectUtil.getInstance().getDefaultSignalsClauseTokenRefereces().iterator(); iterator.hasNext(); ) {
                            String tokenReference = (String) iterator.next();
                            if (signals_clause.predOrNot().getTokenReference().toString().equals(tokenReference)) {
                                isEqual = true;
                            }
                        }

                        String currentEpostTranslated = translateSignalsClause(
                                postVarGen, preVarGen, signals_clause,
                                xPostconditionForContext,
                                "true", 0, oldExprs, oldExprsDecl);
                        epostCode.add(currentEpostTranslated);
                        if (Main.aRacOptions.clientAwareChecking()) {
                            //verifying visibility for translation and composition (combination of spec cases)
                            if (visibility == ACC_PUBLIC) {
                                currentEpostTranslated = translateSignalsClause(
                                        postVarGen, preVarGen, signals_clause,
                                        publicXPostconditionForContext,
                                        "true", 0, publicOldExprs,
                                        publicOldExprsDecl);
                                publicEpostCode.add(currentEpostTranslated);
                            } else if (visibility == ACC_PROTECTED) {
                                currentEpostTranslated = translateSignalsClause(
                                        postVarGen, preVarGen, signals_clause,
                                        protectedXPostconditionForContext,
                                        "true", 0, protectedOldExprs,
                                        protectedOldExprsDecl);
                                protectedEpostCode.add(currentEpostTranslated);
                            } else if (visibility == 0L) {
                                currentEpostTranslated = translateSignalsClause(
                                        postVarGen, preVarGen, signals_clause,
                                        defaultXPostconditionForContext,
                                        "true", 0, defaultOldExprs,
                                        defaultOldExprsDecl);
                                defaultEpostCode.add(currentEpostTranslated);
                            } else if (visibility == ACC_PRIVATE) {
                                currentEpostTranslated = translateSignalsClause(
                                        postVarGen, preVarGen, signals_clause,
                                        privateXPostconditionForContext,
                                        "true", 0, privateOldExprs,
                                        privateOldExprsDecl);
                                privateEpostCode.add(currentEpostTranslated);
                            }
                        }
                    }
                }
                epostCode.add("\t\t   }");
                if (Main.aRacOptions.clientAwareChecking()) {
                    //verifying visibility for translation and composition (combination of spec cases)
                    if (visibility == ACC_PUBLIC) {
                        publicEpostCode.add("\t\t   }");
                    } else if (visibility == ACC_PROTECTED) {
                        protectedEpostCode.add("\t\t   }");
                    } else if (visibility == 0L) {
                        defaultEpostCode.add("\t\t   }");
                    } else if (visibility == ACC_PRIVATE) {
                        privateEpostCode.add("\t\t   }");
                    }
                }
            }
        }
        // accumlate pre-state variables that need to be saved and restored
        // before calling the original method, due to potential recursive calls.
        PreValueVars backupVars = new PreValueVars();
        // determine the names of stack manipulation methods
        String saveMethod = null;
        String restoreMethod = null;
        // generate pre-, and postcondition checking methods advice using
        // Dynamic Crosscutting only call site using CAC technique --- [[[hemr]]]
        if (Main.aRacOptions.clientAwareChecking()) {
            if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(publicOldExprs)) || (publicPreExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(publicOldVarsDecl)))) {
                PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(typeDecl,
                        methodDecl, restoreMethod);
                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                        postStmt,
                        publicPrecondition.toString(),
                        this.getContextValues(publicPrecondition.toString()),
                        publicPreTokenReference.toString(),
                        AspectUtil.changeThisOrSuperRefToAdviceRef(publicNPostcondition.toString(), this.typeDecl),
                        publicEpostCode,
                        publicOldExprs,
                        publicOldExprsDecl,
                        publicPreExprs,
                        publicPreExprsDecl,
                        publicOldVarsDecl,
                        "clientAwareChecking",
                        ACC_PUBLIC,
                        exceptionsInSignalsClauses));
            } else {
                if (AspectUtil.hasPrecondition(publicPrecondition.toString())) {
                    PreconditionMethodAdvice pma = new PreconditionMethodAdvice(
                            typeDecl, methodDecl, hasPublicPrecondition, saveMethod);
                    AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(pma.generate(
                            preStmt,
                            publicPrecondition.toString(),
                            this.getContextValues(publicPrecondition.toString()),
                            publicPreTokenReference.toString(),
                            "clientAwareChecking",
                            ACC_PUBLIC,
                            isEmptySpecCaseWithNonNullPre));
                }
                if (AspectUtil.hasAssertion(publicNPostcondition.toString()) || (publicEpostCode.size() > 0)) {
                    PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                            typeDecl, methodDecl, restoreMethod);
                    JMethodDeclarationType jmdt = npma.generate(
                            postStmt,
                            AspectUtil.changeThisOrSuperRefToAdviceRef(publicNPostcondition.toString(), this.typeDecl),
                            publicEpostCode,
                            publicOldExprs,
                            publicOldExprsDecl,
                            publicPreExprs,
                            publicPreExprsDecl,
                            publicOldVarsDecl,
                            "clientAwareChecking",
                            ACC_PUBLIC);
                    if (AspectUtil.getInstance().isAroundAdvice()) {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                        AspectUtil.getInstance().setAroundAdvice(false);
                    } else {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                    }
                }
            }
            if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(protectedOldExprs)) || (protectedPreExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(protectedOldVarsDecl)))) {
                PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(
                        typeDecl, methodDecl, restoreMethod);
                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                        postStmt,
                        protectedPrecondition.toString(),
                        this.getContextValues(protectedPrecondition.toString()),
                        protectedPreTokenReference.toString(),
                        AspectUtil.changeThisOrSuperRefToAdviceRef(protectedNPostcondition.toString(), this.typeDecl),
                        protectedEpostCode,
                        protectedOldExprs,
                        protectedOldExprsDecl,
                        protectedPreExprs,
                        protectedPreExprsDecl,
                        protectedOldVarsDecl,
                        "clientAwareChecking",
                        ACC_PROTECTED,
                        exceptionsInSignalsClauses));
            } else {
                if (AspectUtil.hasPrecondition(protectedPrecondition.toString())) {
                    PreconditionMethodAdvice pma = new PreconditionMethodAdvice(
                            typeDecl, methodDecl, hasProtectedPrecondition, saveMethod);
                    AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(pma.generate(
                            preStmt,
                            protectedPrecondition.toString(),
                            this.getContextValues(protectedPrecondition.toString()),
                            protectedPreTokenReference.toString(),
                            "clientAwareChecking",
                            ACC_PROTECTED,
                            isEmptySpecCaseWithNonNullPre));
                }
                if (AspectUtil.hasAssertion(protectedNPostcondition.toString()) || (protectedEpostCode.size() > 0)) {
                    PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                            typeDecl, methodDecl, restoreMethod);
                    JMethodDeclarationType jmdt = npma.generate(
                            postStmt,
                            AspectUtil.changeThisOrSuperRefToAdviceRef(protectedNPostcondition.toString(), this.typeDecl),
                            protectedEpostCode,
                            protectedOldExprs,
                            protectedOldExprsDecl,
                            protectedPreExprs,
                            protectedPreExprsDecl,
                            protectedOldVarsDecl,
                            "clientAwareChecking",
                            ACC_PROTECTED
                    );
                    if (AspectUtil.getInstance().isAroundAdvice()) {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                        AspectUtil.getInstance().setAroundAdvice(false);
                    } else {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                    }
                }
            }

            if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(defaultOldExprs)) || (defaultPreExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(defaultOldVarsDecl)))) {
                PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(typeDecl,
                        methodDecl, restoreMethod);
                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                        postStmt,
                        defaultPrecondition.toString(),
                        this.getContextValues(defaultPrecondition.toString()),
                        defaultPreTokenReference.toString(),
                        AspectUtil.changeThisOrSuperRefToAdviceRef(defaultNPostcondition.toString(), this.typeDecl),
                        defaultEpostCode,
                        defaultOldExprs,
                        defaultOldExprsDecl,
                        defaultPreExprs,
                        defaultPreExprsDecl,
                        defaultOldVarsDecl,
                        "clientAwareChecking",
                        0L, // default
                        exceptionsInSignalsClauses));
            } else {
                if (AspectUtil.hasPrecondition(defaultPrecondition.toString())) {
                    PreconditionMethodAdvice pma = new PreconditionMethodAdvice(
                            typeDecl, methodDecl, hasDefaultPrecondition, saveMethod);
                    AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(pma.generate(
                            preStmt,
                            defaultPrecondition.toString(),
                            this.getContextValues(defaultPrecondition.toString()),
                            defaultPreTokenReference.toString(),
                            "clientAwareChecking",
                            0L, //default
                            isEmptySpecCaseWithNonNullPre));
                }
                if (AspectUtil.hasAssertion(defaultNPostcondition.toString()) || (defaultEpostCode.size() > 0)) {
                    PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                            typeDecl, methodDecl, restoreMethod);
                    JMethodDeclarationType jmdt = npma.generate(
                            postStmt,
                            AspectUtil.changeThisOrSuperRefToAdviceRef(defaultNPostcondition.toString(), this.typeDecl),
                            defaultEpostCode,
                            defaultOldExprs,
                            defaultOldExprsDecl,
                            defaultPreExprs,
                            defaultPreExprsDecl,
                            defaultOldVarsDecl,
                            "clientAwareChecking",
                            0L //default
                    );
                    if (AspectUtil.getInstance().isAroundAdvice()) {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                        AspectUtil.getInstance().setAroundAdvice(false);
                    } else {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                    }
                }
            }
            if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(privateOldExprs)) || (privatePreExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(privateOldVarsDecl)))) {
                PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(typeDecl,
                        methodDecl, restoreMethod);
                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                        postStmt,
                        privatePrecondition.toString(),
                        this.getContextValues(privatePrecondition.toString()),
                        privatePreTokenReference.toString(),
                        AspectUtil.changeThisOrSuperRefToAdviceRef(privateNPostcondition.toString(), this.typeDecl),
                        privateEpostCode,
                        privateOldExprs,
                        privateOldExprsDecl,
                        privatePreExprs,
                        privatePreExprsDecl,
                        privateOldVarsDecl,
                        "clientAwareChecking",
                        ACC_PRIVATE,
                        exceptionsInSignalsClauses));
            } else {
                if (AspectUtil.hasPrecondition(privatePrecondition.toString())) {
                    PreconditionMethodAdvice pma = new PreconditionMethodAdvice(
                            typeDecl, methodDecl, hasPrivatePrecondition, saveMethod);
                    AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(pma.generate(
                            preStmt,
                            privatePrecondition.toString(),
                            this.getContextValues(privatePrecondition.toString()),
                            privatePreTokenReference.toString(),
                            "clientAwareChecking",
                            ACC_PRIVATE,
                            isEmptySpecCaseWithNonNullPre));
                }
                if (AspectUtil.hasAssertion(privateNPostcondition.toString()) || (privateEpostCode.size() > 0)) {
                    PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                            typeDecl, methodDecl, restoreMethod);
                    JMethodDeclarationType jmdt = npma.generate(
                            postStmt,
                            AspectUtil.changeThisOrSuperRefToAdviceRef(privateNPostcondition.toString(), this.typeDecl),
                            privateEpostCode,
                            privateOldExprs,
                            privateOldExprsDecl,
                            privatePreExprs,
                            privatePreExprsDecl,
                            privateOldVarsDecl,
                            "clientAwareChecking",
                            ACC_PRIVATE
                    );

                    if (AspectUtil.getInstance().isAroundAdvice()) {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                        AspectUtil.getInstance().setAroundAdvice(false);
                    } else {
                        AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                    }
                }
            }
        } else {
            if (isMethodCrosscutSpecChecking) {
                // does not matter if we use execution or call site... in the crosscutting contract specification the
                // the instrumentation comes directly from the pointcut declaration --- [[[hemr]]]
                if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(oldExprs) || (preExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(oldVarsDecl))))) {
                    PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(typeDecl,
                            methodDecl, restoreMethod);
                    AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdviceXCS(npma.generate(
                            postStmt,
                            precondition.toString(),
                            this.getContextValues(precondition.toString()),
                            preTokenReference.toString(),
                            AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                            epostCode,
                            oldExprs,
                            oldExprsDecl,
                            preExprs,
                            preExprsDecl,
                            oldVarsDecl,
                            "executionSite",
                            -1,
                            exceptionsInSignalsClauses));
                } else {
                    if (AspectUtil.hasPrecondition(precondition.toString())) {
                        PreconditionMethodAdvice pma = new PreconditionMethodAdvice(typeDecl,
                                methodDecl, hasPrecondition, saveMethod);
                        AspectUtil.getInstance().appendPreconditionNewMethodsAdviceXCS(pma.generate(
                                preStmt,
                                precondition.toString(),
                                this.getContextValues(precondition.toString()),
                                preTokenReference.toString(),
                                "executionSite",
                                -1,
                                isEmptySpecCaseWithNonNullPre));
                    }
                    if (AspectUtil.hasAssertion(nPostcondition.toString()) || (epostCode.size() > 0)) {
                        PostconditionMethodAdvice npma = new PostconditionMethodAdvice(typeDecl,
                                methodDecl, restoreMethod);
                        JMethodDeclarationType jmdt = npma.generate(
                                postStmt,
                                AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                                epostCode,
                                oldExprs,
                                oldExprsDecl,
                                preExprs,
                                preExprsDecl,
                                oldVarsDecl,
                                "executionSite",
                                -1
                        );
                        if (AspectUtil.getInstance().isAroundAdvice()) {
                            AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdviceXCS(jmdt);
                            AspectUtil.getInstance().setAroundAdvice(false);
                        } else {
                            AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdviceXCS(jmdt);
                        }
                    }
                }
            } else {
                // call site
                if (Main.aRacOptions.callSiteInstrumentation()) {
                    if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(oldExprs)) || (preExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(oldVarsDecl)))) {
                        PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(
                                typeDecl, methodDecl, restoreMethod);
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                                postStmt,
                                precondition.toString(),
                                this.getContextValues(precondition.toString()),
                                preTokenReference.toString(),
                                AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                                epostCode,
                                oldExprs,
                                oldExprsDecl,
                                preExprs,
                                preExprsDecl,
                                oldVarsDecl,
                                "callSite",
                                -1,
                                exceptionsInSignalsClauses));
                    } else {
                        if (AspectUtil.hasPrecondition(precondition.toString())) {
                            PreconditionMethodAdvice pma = new PreconditionMethodAdvice(
                                    typeDecl, methodDecl, hasPrecondition, saveMethod);
                            AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(pma.generate(
                                    preStmt,
                                    precondition.toString(),
                                    this.getContextValues(precondition.toString()),
                                    preTokenReference.toString(),
                                    "callSite",
                                    -1,
                                    isEmptySpecCaseWithNonNullPre));
                        }
                        if (AspectUtil.hasAssertion(nPostcondition.toString()) || (epostCode.size() > 0)) {
                            PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                                    typeDecl, methodDecl, restoreMethod);
                            JMethodDeclarationType jmdt = npma.generate(
                                    postStmt,
                                    AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                                    epostCode,
                                    oldExprs,
                                    oldExprsDecl,
                                    preExprs,
                                    preExprsDecl,
                                    oldVarsDecl,
                                    "callSite",
                                    -1
                            );
                            if (AspectUtil.getInstance().isAroundAdvice()) {
                                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                                AspectUtil.getInstance().setAroundAdvice(false);
                            } else {
                                AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                            }
                        }
                    }
                }
                if (!Main.aRacOptions.noExecutionSiteInstrumentation()) {
                    // execution site
                    if (((AspectUtil.getInstance().hasElementsStoredOldExpressions(oldExprs)) || (preExprs.size() > 0) || (AspectUtil.getInstance().hasElementsStoredOldExpressions(oldVarsDecl)))) {
                        PostconditionMethodAdvice2 npma = new PostconditionMethodAdvice2(typeDecl,
                                methodDecl, restoreMethod);
                        AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(npma.generate(
                                postStmt,
                                precondition.toString(),
                                this.getContextValues(precondition.toString()),
                                preTokenReference.toString(),
                                AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                                epostCode,
                                oldExprs,
                                oldExprsDecl,
                                preExprs,
                                preExprsDecl,
                                oldVarsDecl,
                                "executionSite",
                                -1,
                                exceptionsInSignalsClauses));
                    } else {
                        if (AspectUtil.hasPrecondition(precondition.toString())) {
                            PreconditionMethodAdvice prema = new PreconditionMethodAdvice(
                                    typeDecl, methodDecl, hasPrecondition, saveMethod);
                            AspectUtil.getInstance().appendPreconditionNewMethodsAdvice(prema.generate(
                                    preStmt,
                                    precondition.toString(),
                                    this.getContextValues(precondition.toString()),
                                    preTokenReference.toString(),
                                    "executionSite",
                                    -1,
                                    isEmptySpecCaseWithNonNullPre));
                        }
                        if (AspectUtil.hasAssertion(nPostcondition.toString()) || (epostCode.size() > 0)) {
                            PostconditionMethodAdvice npma = new PostconditionMethodAdvice(
                                    typeDecl, methodDecl, restoreMethod);
                            JMethodDeclarationType jmdt = npma.generate(
                                    postStmt,
                                    AspectUtil.changeThisOrSuperRefToAdviceRef(nPostcondition.toString(), this.typeDecl),
                                    epostCode,
                                    oldExprs,
                                    oldExprsDecl,
                                    preExprs,
                                    preExprsDecl,
                                    oldVarsDecl,
                                    "executionSite",
                                    -1
                            );
                            if (AspectUtil.getInstance().isAroundAdvice()) {
                                AspectUtil.getInstance().appendPostconditionNewMethodsAroundAdvice(jmdt);
                                AspectUtil.getInstance().setAroundAdvice(false);
                            } else {
                                AspectUtil.getInstance().appendPostconditionNewMethodsAfterAdvice(jmdt);
                            }
                        }
                    }
                }
            }
        }
        return backupVars;
    }

    private long extractVisibilitySpecs(int specCaseIndex) {
        long result = -10;
        JmlSpecCase[] jsc = ((JmlSpecification) this.methodDecl.methodSpecification()).specCases();
        SpecCaseCollector specs = new SpecCaseCollector(desugaredSpec);
        if (jsc.length < specs.specCases.size()) {
            int count = 0;
            scan:
            {
                for (int i = 0; i < jsc.length; i++) {
                    if (jsc[i] instanceof JmlBehaviorSpec) {
                        JmlBehaviorSpec bspec = (JmlBehaviorSpec) jsc[specCaseIndex];
                        if (bspec.isNestedSpec()) {
                            int innerSize = bspec.specCase().specBody()
                                    .specCases().length;
                            for (int j = 0; j < innerSize; j++) {
                                int index = j + count;
                                if (index == specCaseIndex) {
                                    result = bspec.privacy();
                                    break scan;
                                }
                            }
                            count += (bspec.specCase().specBody()
                                    .specCases().length - 1);
                        } else {
                            if (count == specCaseIndex) {
                                result = bspec.privacy();
                                break scan;
                            }
                        }
                    } else if (jsc[i] instanceof JmlNormalBehaviorSpec) {
                        JmlNormalBehaviorSpec nbspec = (JmlNormalBehaviorSpec) jsc[i];
                        if (nbspec.isNestedSpec()) {
                            int innerSize = nbspec.specCase().specBody()
                                    .specCases().length;
                            for (int j = 0; j < innerSize; j++) {
                                int index = j + count;
                                if (index == specCaseIndex) {
                                    result = nbspec.privacy();
                                    break scan;
                                }
                            }
                            count += (nbspec.specCase().specBody()
                                    .specCases().length - 1);
                        } else {
                            if (count == specCaseIndex) {
                                result = nbspec.privacy();
                                break scan;
                            }
                        }
                    } else if (jsc[i] instanceof JmlExceptionalBehaviorSpec) {
                        JmlExceptionalBehaviorSpec ebspec = (JmlExceptionalBehaviorSpec) jsc[i];
                        if (ebspec.isNestedSpec()) {
                            int innerSize = ebspec.specCase().specBody()
                                    .specCases().length;
                            for (int j = 0; j < innerSize; j++) {
                                int index = j + count;
                                if (index == specCaseIndex) {
                                    result = ebspec.privacy();
                                    break scan;
                                }
                            }
                            count += (ebspec.specCase().specBody()
                                    .specCases().length - 1);
                        } else {
                            if (count == specCaseIndex) {
                                result = ebspec.privacy();
                                break scan;
                            }
                        }
                    } else if (jsc[i] instanceof JmlGenericSpecCase) {

                        JmlGenericSpecCase jgsp = (JmlGenericSpecCase) jsc[i];
                        if (jgsp.specBody().specCases() != null) {
                            int innerSize = jgsp.specBody().specCases().length;
                            for (int j = 0; j < innerSize; j++) {
                                int index = j + count;
                                if (index == specCaseIndex) {
                                    if (this.methodDecl.isSpecPublic()) {
                                        result = ACC_PUBLIC;
                                        break scan;
                                    } else if (this.methodDecl
                                            .isSpecProtected()) {
                                        result = ACC_PROTECTED;
                                        break scan;
                                    } else if (this.methodDecl.isPrivate()) {
                                        result = ACC_PRIVATE;
                                        break scan;
                                    } else {
                                        result = privacy(this.methodDecl
                                                .getMethod().modifiers());
                                        break scan;
                                    }
                                }
                            }
                            count += (jgsp.specBody()
                                    .specCases().length - 1);
                        } else {
                            if (count == specCaseIndex) {
                                if (this.methodDecl.isSpecPublic()) {
                                    result = ACC_PUBLIC;
                                    break scan;
                                } else if (this.methodDecl
                                        .isSpecProtected()) {
                                    result = ACC_PROTECTED;
                                    break scan;
                                } else if (this.methodDecl.isPrivate()) {
                                    result = ACC_PRIVATE;
                                    break scan;
                                } else {
                                    result = privacy(this.methodDecl
                                            .getMethod().modifiers());
                                    break scan;
                                }
                            }
                        }
                    }
                    count++;
                }
            }
        } else {
            if (jsc[specCaseIndex] instanceof JmlBehaviorSpec) {
                JmlBehaviorSpec bspec = (JmlBehaviorSpec) jsc[specCaseIndex];
                result = bspec.privacy();
            } else if (jsc[specCaseIndex] instanceof JmlNormalBehaviorSpec) {
                JmlNormalBehaviorSpec nbspec = (JmlNormalBehaviorSpec) jsc[specCaseIndex];
                result = nbspec.privacy();
            } else if (jsc[specCaseIndex] instanceof JmlExceptionalBehaviorSpec) {
                JmlExceptionalBehaviorSpec ebspec = (JmlExceptionalBehaviorSpec) jsc[specCaseIndex];
                result = ebspec.privacy();
            } else if (jsc[specCaseIndex] instanceof JmlGenericSpecCase) {
                if (this.methodDecl.isSpecPublic()) {
                    result = ACC_PUBLIC;
                } else if (this.methodDecl.isSpecProtected()) {
                    result = ACC_PROTECTED;
                } else if (this.methodDecl.isPrivate()) {
                    result = ACC_PRIVATE;
                } else {
                    result = privacy(this.methodDecl.getMethod()
                            .modifiers());
                }
            }
        }
        return result;
    }

    protected long privacy(long modifiers) {
        if (hasFlag(modifiers, ACC_SPEC_PUBLIC | ACC_PUBLIC))
            return ACC_PUBLIC;
        else if (hasFlag(modifiers, ACC_SPEC_PROTECTED | ACC_PROTECTED))
            return ACC_PROTECTED;
        else if (hasFlag(modifiers, ACC_PRIVATE))
            return ACC_PRIVATE;
        else
            return 0L; // package
    }

//	private boolean isValidSpecCases(long methodVisibility, SpecCaseCollector specs){
//		boolean isValidSpecCases = false;
//		int preVarCount = 0;
//		long specVisibility = 0;
//		Iterator iter = specs.iterator();
//		while (iter.hasNext()) {
//			SpecCase c = (SpecCase) iter.next();
//			specVisibility = extractVisibilitySpecs(preVarCount);
//			if(methodVisibility == specVisibility){
//				isValidSpecCases = true;
//				break;
//			}
//			preVarCount++;
//		}
//		return isValidSpecCases;
//	}

    private boolean isValidSpecCases(long methodVisibility, JmlSpecCase[] specs) {
        boolean isValidSpecCases = false;
        int preVarCount = 0;
        long specVisibility = 0;

        for (int i = 0; i < specs.length; i++) {
            JmlSpecCase c = (JmlSpecCase) specs[i];
            specVisibility = extractVisibilitySpecs(preVarCount);
            if (methodVisibility == specVisibility) {
                isValidSpecCases = true;
                break;
            }
            preVarCount++;
        }
        return isValidSpecCases;
    }

    /**
     * @param precondition
     * @param transPred
     */
    private void combineSpecCasesForPrecondition(StringBuffer precondition,
                                                 String transPred) {

        if (transPred.equals("true") || transPred.equals("false")) {
            transPred = "(" + transPred + ")";
        }
        if (precondition.length() == 0) {
            precondition.append(transPred);
        } else {
            precondition.append(" || ");
            precondition.append(transPred);
            precondition.insert(0, "(");
            precondition.append(")");
        }
    }

    /**
     * @param specCase
     * @param transPred
     */
    private void combineSpecCases(StringBuffer specCase,
                                  String transPred) {
        if (specCase.length() == 0) {
            specCase.append(transPred);
        } else {
            specCase.append(" && ");
            specCase.append(transPred);
            specCase.insert(0, "(");
            specCase.append(")");
        }
    }

    private String combinePreAndNPost(String transPre,
                                      String transNPost) {
        if (transPre.equals("")) {
            return "(" + transNPost + ")";
        } else {
            return "(!(" + transPre + ")" + " || " + "" + transNPost + ")";
        }
    }

    private void combineTokenReferenceForPred(StringBuffer predTokenReference, String tokenReference) {
        if (predTokenReference.length() > 0) {
            predTokenReference.append(", and \\n[spec-case]: ").append(tokenReference);
        } else {
            predTokenReference.append("[spec-case]: ").append(tokenReference);
        }
    }

    private List getAllInheritedFields() {
        Collection collect = null;
        List listFields = new ArrayList();

        try {
            CClassType superType = this.typeDecl.getCClass().getSuperType();
            collect = superType.getCClass().fields();
            CClassType[] interfaces = this.typeDecl.getCClass().getInterfaces();

            while (!superType.ident().equals("Object")) {
                collect = superType.getCClass().fields();
                for (Iterator iter = collect.iterator(); iter.hasNext(); ) {
                    listFields.add(iter.next());
                }

                superType = superType.getCClass().getSuperType();
            }

            for (int i = 0; i < interfaces.length; i++) {
                collect = interfaces[i].getCClass().fields();
                for (Iterator iter = collect.iterator(); iter.hasNext(); ) {
                    listFields.add(iter.next());
                }
            }
        } catch (Exception e) {
        }

        return listFields;
    }

    private boolean hasFieldReferenceInPrecondition(String pred) {
        List inheritedFields = this.getAllInheritedFields();
        JFormalParameter[] parameters = this.methodDecl.parameters();
        final List paramFields = new ArrayList();
        boolean result = false;

        pred = pred.replace(".", " ");
        String[] predWords = pred.split(" ");

        if (parameters != null) {
            for (int i = 0; i < parameters.length; i++) {
                parameters[i].accept(new JmlAbstractVisitor() {
                    public void visitJmlFormalParameter(JmlFormalParameter self) {
                        String ident = self.ident();
                        paramFields.add(ident);
                    }
                });
            }
        }

        //handling inherited fields
        if (inheritedFields.size() > 0) {
            for (int j = 0; j < predWords.length; j++) {
                String precedingPredWord = "";
                if (j >= 1) {
                    precedingPredWord = predWords[j - 1].replace("(", "");
                }
                for (Iterator iter = inheritedFields.iterator(); iter.hasNext(); ) {
                    Object inheritedFieldsType = iter.next();
                    if (inheritedFieldsType instanceof JmlSourceField) {
                        JmlSourceField inheritedField = (JmlSourceField) inheritedFieldsType;
                        if (predWords[j].replace("(", "").equals(inheritedField.ident())) {
                            if (precedingPredWord.equals("this")) {
                                result = true;
                            } else {
                                if (!paramFields.contains(inheritedField.ident())) {
                                    result = true;
                                }
                            }
                        }
                    } else if (inheritedFieldsType instanceof CBinaryField) {
                        CBinaryField inheritedField = (CBinaryField) inheritedFieldsType;
                        if (predWords[j].replace("(", "").equals(inheritedField.ident())) {
                            if (precedingPredWord.equals("this")) {
                                result = true;
                            } else {
                                if (!paramFields.contains(inheritedField.ident())) {
                                    result = true;
                                }
                            }
                        }
                    }
                }
            }
        }

        //handling local fields
        if (typeDecl.fields().length > 0) {
            JFieldDeclarationType localFields[] = this.typeDecl.fields();
            for (int j = 0; j < predWords.length; j++) {
                String precedingPredWord = "";
                if (j >= 1) {
                    precedingPredWord = predWords[j - 1].replace("(", "");
                }
                for (int i = 0; i < localFields.length; i++) {
                    if (predWords[j].replace("(", "").equals(localFields[i].ident())) {
                        if (precedingPredWord.equals("this")) {
                            result = true;
                        } else {
                            if (!paramFields.contains(localFields[i].ident())) {
                                result = true;
                            }
                        }
                    }
                }
            }
        }
        return result;
    }

    private boolean hasMethodCallExpInPrecondition(String pred) {
        Pattern p = Pattern.compile("[\\w]+[\\(]+[\\w]*[,]*[\\s]*[\\w]*[\\)]+");
        Matcher m = p.matcher(pred);
        return m.find();
    }

    protected String getContextValues(String predicate) {
        final StringBuffer code = new StringBuffer();
        List inheritedFields = getAllInheritedFields();
        JFieldDeclarationType localFields[] = this.typeDecl.fields();
        JFormalParameter[] parameters = this.methodDecl.parameters();
        final List paramFields = new ArrayList();
        List includedVariables = new ArrayList();
        boolean hasContext = false;

        if (parameters != null) {
            for (int i = 0; i < parameters.length; i++) {
                parameters[i].accept(new JmlAbstractVisitor() {
                    public void visitJmlFormalParameter(JmlFormalParameter self) {
                        String ident = self.ident();
                        paramFields.add(ident);
                    }
                });
            }
        }
        predicate = predicate.replace("(", " ").replace(")", " ").replace(";", " ").replace(".", " ");
        String[] predWords = predicate.split(" ");

        //handling local fields
        hasContext = this.localFieldHandler(code, localFields, paramFields,
                hasContext, predWords);
        //handling inherited fields
        if (inheritedFields.size() > 0) {
            for (int j = 0; j < predWords.length; j++) {
                for (Iterator iter = inheritedFields.iterator(); iter.hasNext(); ) {
                    Object inheritedFieldsType = iter.next();
                    if (inheritedFieldsType instanceof JmlSourceField) {
                        JmlSourceField inheritedField = (JmlSourceField) inheritedFieldsType;
                        hasContext = this.inheritedFieldsHandler(code, paramFields, hasContext,
                                predWords, j, inheritedField);
                    } else if (inheritedFieldsType instanceof CBinaryField) {
                        CBinaryField inheritedField = (CBinaryField) inheritedFieldsType;
                        hasContext = this.inheritedFieldsHandler(code, paramFields, hasContext,
                                predWords, j, inheritedField);
                    }
                }
            }
        }
        //handling param fields
        for (int j = 0; j < predWords.length; j++) {
            String precedingPredWord = "";

            if (j >= 1) {
                precedingPredWord = predWords[j - 1].replace("(", "");
            }

            if (paramFields.size() > 0) {
                for (Iterator iterator = paramFields.iterator(); iterator
                        .hasNext(); ) {
                    String paramField = (String) iterator.next();
                    if (predWords[j].replace("(", "").equals(paramField)) {
                        if (!precedingPredWord.equals("this")) {
                            if (!includedVariables.contains(paramField)) {
                                if (hasContext) {
                                    code.append("+\"\\n");
                                }
                                code.append("\\t\\\'");
                                code.append(paramField);
                                code.append("\\\' is \"+" + paramField);
                                hasContext = true;
                                includedVariables.add(paramField);
                            }
                        }
                    }
                }
            }
        }
        return code.toString();
    }

    private boolean inheritedFieldsHandler(final StringBuffer code,
                                           final List paramFields, boolean hasContext, String[] predWords,
                                           int j, Object inheritedField) {

        if (inheritedField instanceof JmlSourceField) {
            hasContext = inheritedFieldCodeTemplate(code, paramFields, hasContext, predWords,
                    j, ((JmlSourceField) inheritedField).ident(), ((JmlSourceField) inheritedField).isFieldStatic());
        } else {
            hasContext = inheritedFieldCodeTemplate(code, paramFields, hasContext, predWords,
                    j, ((CBinaryField) inheritedField).ident(), ((CBinaryField) inheritedField).isFieldStatic());
        }

        return hasContext;
    }

    private boolean inheritedFieldCodeTemplate(final StringBuffer code,
                                               final List paramFields, boolean hasContext, String[] predWords,
                                               int j, String inheritedField, boolean isStaticField) {
        List includedVariables = new ArrayList();
        String precedingPredWord = "";

        if (j >= 1) {
            precedingPredWord = predWords[j - 1].replace("(", "");
        }

        if (predWords[j].replace("(", "").equals(inheritedField)) {
            if (precedingPredWord.equals("this")) {
                //				if (hasContext) {
                //					code.append("+\"\\n");
                //				}
                //				code.append("\\t\\\'");
                if (isStaticField) {
                    if (!includedVariables.contains(typeDecl.ident() + "." + inheritedField)) {
                        if (hasContext) {
                            code.append("+\"\\n");
                        }
                        code.append("\\t\\\'");
                        code.append(this.typeDecl.getCClass().getJavaName() + "."
                                + inheritedField);
                        code.append("\\\' is \"+"
                                + this.typeDecl.getCClass().getJavaName() + "."
                                + inheritedField);
                        hasContext = true;
                        includedVariables.add(this.typeDecl.getCClass().getJavaName()
                                + "." + inheritedField);
                    }
                } else {
                    if (!includedVariables.contains("this." + inheritedField)) {
                        if (hasContext) {
                            code.append("+\"\\n");
                        }
                        code.append("\\t\\\'");
                        code.append("this." + inheritedField);
                        code.append("\\\' is \"+" + "object$rac."
                                + inheritedField);
                        hasContext = true;
                        includedVariables.add("this." + inheritedField);
                    }
                }
            } else {
                if (!paramFields.contains(inheritedField)) {
                    if (!includedVariables.contains(inheritedField)) {
                        if (hasContext) {
                            code.append("+\"\\n");
                        }
                        code.append("\\t\\\'");
                        if (isStaticField) {
                            code.append(this.typeDecl.getCClass().getJavaName() + "."
                                    + inheritedField);
                            code.append("\\\' is \"+"
                                    + this.typeDecl.getCClass().getJavaName() + "."
                                    + inheritedField);
                            hasContext = true;
                        } else {
                            code.append("this." + inheritedField);
                            code.append("\\\' is \"+" + "object$rac."
                                    + inheritedField);
                            hasContext = true;
                        }
                    }
                }
                includedVariables.add(inheritedField);
            }
        }
        return hasContext;
    }

    /**
     * @param code
     * @param localFields
     * @param paramFields
     * @param hasContext
     * @param predWords
     * @return
     */
    private boolean localFieldHandler(final StringBuffer code,
                                      JFieldDeclarationType[] localFields, final List paramFields,
                                      boolean hasContext, String[] predWords) {
        List includedVariables = new ArrayList();

        for (int j = 0; j < predWords.length; j++) {
            String precedingPredWord = "";

            if (j >= 1) {
                precedingPredWord = predWords[j - 1].replace("(", "");
            }

            for (int i = 0; i < localFields.length; i++) {
                if (predWords[j].replace("(", "").equals(localFields[i].ident())) {
                    if (precedingPredWord.equals("this")) {
                        if (localFields[i].getField().isFieldStatic()) {
                            if (hasContext) {
                                code.append("+\"\\n");
                            }
                            code.append("\\t\\\'");
                            if (!includedVariables.contains(typeDecl.ident() + "." + localFields[i].ident())) {
                                code.append(this.typeDecl.getCClass().getJavaName() + "."
                                        + localFields[i].ident());
                                code.append("\\\' is \"+"
                                        + this.typeDecl.ident() + "."
                                        + localFields[i].ident());
                                hasContext = true;
                                includedVariables.add(typeDecl.getCClass().getJavaName()
                                        + "." + localFields[i].ident());
                            }
                        } else {
                            if (!includedVariables.contains("this." + localFields[i].ident())) {
                                if (hasContext) {
                                    code.append("+\"\\n");
                                }
                                code.append("\\t\\\'");
                                code.append("this." + localFields[i].ident());
                                if (localFields[i].ident().equals(RacConstants.VN_ASPECTJ_THISJOINPOINT)) {
                                    code.append("\\\' is \"+" + localFields[i].ident());
                                } else {
                                    code.append("\\\' is \"+" + "object$rac."
                                            + localFields[i].ident());
                                }

                                hasContext = true;
                                includedVariables.add("this." + localFields[i].ident());
                            }
                        }
                    } else if (precedingPredWord.equals("rac$result")) {
                        if (!paramFields.contains(localFields[i].ident())) {
                            if (!includedVariables.contains(localFields[i].ident())) {
                                if (hasContext) {
                                    code.append("+\"\\n");
                                }
                                code.append("\\t\\\'");
                                if (localFields[i].getField().isFieldStatic()) {
                                    code.append(typeDecl.getCClass().getJavaName() + "."
                                            + localFields[i].ident());
                                    code.append("\\\' is \"+"
                                            + this.typeDecl.getCClass().getJavaName() + "."
                                            + localFields[i].ident());
                                    hasContext = true;
                                } else {
                                    code.append("this." + localFields[i].ident());
                                    code.append("\\\' is \"+" + "rac$result."
                                            + localFields[i].ident());
                                    hasContext = true;
                                }
                            }
                        }
                        includedVariables.add(localFields[i].ident());
                    } else {
                        if (!paramFields.contains(localFields[i].ident())) {
                            if (!includedVariables.contains(localFields[i].ident())) {
                                if (hasContext) {
                                    code.append("+\"\\n");
                                }
                                code.append("\\t\\\'");
                                if (localFields[i].getField().isFieldStatic()) {
                                    code.append(typeDecl.getCClass().getJavaName() + "."
                                            + localFields[i].ident());
                                    code.append("\\\' is \"+"
                                            + this.typeDecl.getCClass().getJavaName() + "."
                                            + localFields[i].ident());
                                    hasContext = true;
                                } else {
                                    code.append("this." + localFields[i].ident());
                                    code.append("\\\' is \"+" + "object$rac."
                                            + localFields[i].ident());
                                    hasContext = true;
                                }
                            }
                        }
                        includedVariables.add(localFields[i].ident());
                    }
                }
            }
        }
        return hasContext;
    }

    /**
     * Translates specification variable declarations. Initializers
     * are translated and returned with their new private field
     * declarations. The caller is responsible for properly declaring
     * the fields for the specification variables and execute the
     * translated initializers in the appropriate place, e.g., in the
     * method prolog.
     * <p/>
     * <pre><jml>
     * requires varDecls != null && varGen != null;
     * ensures \fresh(\result) && (\forall Object o; \result.contains(o);
     *         o instanceof RacNode);
     * </jml></pre>
     *
     * @param varDecls declarations to be translated
     * @param varGen   variable generator for fresh variable names
     * @return list of <code>RacNode</code>s, representing translated
     * initializers with the corresponding new field
     * declarations. The field declarations are
     * piggybacked in the <code>name</code> fields of nodes.
     */
    protected List translateSpecVarDecls(JmlSpecVarDecl[] varDecls,
                                         VarGenerator varGen) {
        // list of RacNode's representing translated initializers
        List result = new ArrayList();

        for (int i = 0; i < varDecls.length; i++) {
            // already processed, i.e., when desugared?
            if (varDecls[i].racGenerated()) {
                continue;
            }
            varDecls[i].setRacGenerated();

            if (varDecls[i] instanceof JmlLetVarDecl) {
                result.addAll(translateLetVarDecl(varDecls[i], varGen));
            } else {
                result.addAll(translateForAllVarDecl(varDecls[i], varGen));
            }
        }
        return result;
    }

    /**
     * Translates the given old variable declarations. The
     * initializers are translated and and returned with new instance
     * variable declarations. The caller is responsible for properly
     * declaring the new instance variables and execute the code to
     * stores the values of initializers to the new fields.
     * <p/>
     * <pre><jml>
     * requires varDecl != null && varGen != null;
     * ensures \fresh(\result) && (\forall Object o; \result.contains(o);
     *         o instanceof RacNode);
     * </jml></pre>
     *
     * @param varDecl declaration to be translated
     * @param varGen  variable generator for fresh variable names
     * @return list of <code>RacNode</code>s representing translated
     * code with the new instance field declarations.
     * The field declarations are piggybacked in the
     * <code>name</code> fields of RacNode.
     */
    protected List translateLetVarDecl(JmlSpecVarDecl varDecl,
                                       VarGenerator varGen) {
        // list of RacNodes representing translated code
        List result = new ArrayList();

        JmlVariableDefinition[] varDefs = (JmlVariableDefinition[])
                ((JmlLetVarDecl) varDecl).specVariableDeclarators();

        for (int j = 0; j < varDefs.length; j++) {
            if (!varDefs[j].hasInitializer()) {
                // jml gurantees this not to reach!
                //@ unreachable;
                fail("Reached unreachable!");
            }

            // create a fresh variable unique in the class scope. This
            // prevents name crashes when the variable becomes a new
            // privat field; i.e, name crashes among let variables
            // and existing fields.
            //String oldVar = varGen.freshOldVar();
            CType type = varDefs[j].getType();

            // change the identifier so that from now on it is printed as
            // code for unwrapping the new field.
            //			varDefs[j].setIdent(
            //			TransUtils.unwrapObject(type, oldVar + ".value()"));
            //varDefs[j].setRacField(oldVar);

            // generates code that evaluates the initializer

            // disable contextual interpretation so that it is handled
            // when the field variable is actually referenced.
            RacContext ctx = RacContext.createNeutral();
            String var = "";
            var = varGen.freshVar() + "$old"; // [[[hemr]]]
            varDefs[j].setIdent(var);
            //			String val = TransExpression.defaultValue(type);
            TransExpression2 trans = new TransExpression2(varGen, ctx,
                    varDefs[j].expr(), var, typeDecl, "");
            result.add(type + " " + var + "/" + var + " = " + trans.stmtAsString());
        }
        return result;
    }

    /**
     * Translates the given forall variable declarations. They are
     * translated into the non-executable values, and and returned with
     * their corresponding instance variable declarations. The caller
     * is responsible for properly declaring the instance variables and
     * execute the code stores non-executable values to the fields.
     * <p/>
     * <pre><jml>
     * requires varDecl != null && varGen != null;
     * ensures \fresh(\result) && (\forall Object o; \result.contains(o);
     *         o instanceof RacNode);
     * </jml></pre>
     *
     * @param varDecl declaration to be translated
     * @param varGen  variable generator for fresh variable names
     * @return list of <code>RacNode</code>s representing translated
     * code with the corresponding instance field declarations.
     * The field declarations are piggybacked in the
     * <code>name</code> fields of RacNode.
     */
    protected List translateForAllVarDecl(JmlSpecVarDecl varDecl,
                                          VarGenerator varGen) {
        // list of RacNodes representing translated code
        List result = new ArrayList();

        JVariableDefinition[] varDefs =
                ((JmlForAllVarDecl) varDecl).quantifiedVarDecls();
        for (int j = 0; j < varDefs.length; j++) {
            // create a fresh variable unique in the class scope. This
            // prevents name crashes when the variable becomes a new
            // privat field; i.e, name crashes among forall variables
            // and existing fields.
            String oldVar = varGen.freshOldVar();

            // generates code that stores the non-executable value to the
            // fresh field.
            CType type = varDefs[j].getType();
            RacNode node = RacParser.parseStatement(
                    "if (true) {\n" +
                            "  " + oldVar + " = " + TN_JMLVALUE + ".ofNonExecutable();\n" +
                            "}");

            // piggy-back a new field declaration to the code
            node.setVarDecl(PreValueVars.createJmlValueVar(
                    methodDecl.isStatic(), oldVar));

            // change the identifier so that it is now printed as
            // code for unwrapping the new field.
            varDefs[j].setIdent(TransUtils.unwrapObject(type, oldVar + ".value()"));
            result.add(node);
        }
        return result;
    }

    private String generateXPostErrorMessage(String context,
                                             String tokenReference) {

        boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);
        String methodDescription;
        if (isMethodCrosscutSpecChecking) {
            methodDescription = "by method \"+thisJoinPoint.getSignature().getDeclaringTypeName()+\".\"+thisJoinPoint.getSignature().getName()+\"";
        } else {
            methodDescription = "by method " + this.methodDecl.getMethod().getJavaName();
        }
        final String SPEC_ERROR_MSG = AssertionMethod.SPEC_ERROR_MSG;
        final String CODE_ERROR_MSG = AssertionMethod.CODE_ERROR_MSG;
        final String NONE = "";
        String result = "";

        if (this.methodDecl.body() != null) {
            JStatement js[];
            try {
                js = this.methodDecl.body().body();
                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContextForXPost =
                        (js.length == 0 ? "\"" :
                                ", line " +
                                        +js[js.length - 1].getTokenReference().line() + " ("
                                        + this.typeDecl.getCClass().getJavaName() + ".java:"
                                        + js[js.length - 1].getTokenReference().line() + ")\"");

                String bodyCodeReferenceWithContextForXPost = bodyCodeReferenceWithoutContextForXPost + (context.length() > 0 ? "+\", when \\n\"" + context : "");
                if (!tokenReference.equals(NONE)) {
                    String tmp = ", " + tokenReference + ", and \\n" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                    result = "\"" + methodDescription + SPEC_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                    result += tmp + bodyCodeReferenceWithContextForXPost;
                } else {
                    String tmp = "\"" + methodDescription + CODE_ERROR_MSG + "File \\\"" + this.typeDecl.getCClass().getJavaName() + ".java\\\"";
                    result += tmp + bodyCodeReferenceWithContextForXPost;
                }

                if ((js.length == 0) && (context.length() > 0)) {
                    result = result + "+ \", when \\n\"" + context;
                }
            } catch (NullPointerException e) {
                if (context.startsWith("\\")) {
                    context = "+\"" + context;
                }
                String bodyCodeReferenceWithoutContextForXPost = "\"";
                String bodyCodeReferenceWithContextForXPost = bodyCodeReferenceWithoutContextForXPost + (context.length() > 0 ? "+\", when \\n\"" + context : "");
                String tmp;
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
        } else {
            // If has no body, which occurs with methods inside Interfaces, the only possibility here is "XPost_Error"
            // because for preconditions, only intertype declarations are generated... (there is no precondition_error code generated)
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
        return result;
    }

    public static boolean isValidSignalsClause(CClass type) {
        boolean result = true;
        CClass clazz = type;
        do {
            if (clazz.getJavaName().equals("java.lang.Error")) {
                result = false;
            }
            clazz = clazz.getSuperClass();
        } while ((clazz.getSuperClass() != null) && (!clazz.getSuperClass().getJavaName().equals("java.lang.Object")));
        return result;
    }

    /**
     * Translates the given <code>signals</code> clause. The overall
     * translation rule for exceptional postconditions is roughly
     * defined as follows.
     * <p/>
     * <pre>
     *  [[signals (Ei ei) Pi]] =
     *    if (e instanceof Ei) {
     *       Ei ei = (Ei) e;
     *       boolean vi = false;
     *       [[Pi, vi]]
     *       b = b && vi;
     *    }
     *    check(b);
     *    if (e instanceof java.lang.RuntimeException)
     *       throw (java.lang.RuntimeException) e;
     *    else if (e instanceof java.lang.Error)
     *       throw (java.lang.Error) e;
     *    if (e instanceof CEi)
     *       throw (CEi) e;
     * </pre>
     */
    protected String translateSignalsClause(
            VarGenerator varGen, VarGenerator oldVarGen, JmlSignalsClause sigClause,
            StringBuffer xPostconditionForContext, String preVar, int index,
            HashMap oldExprs, HashMap oldExprsDecl) {
        CType type = sigClause.type();
        if (!isValidSignalsClause(type.getCClass())) {
            JmlRacGenerator.fail(sigClause.getTokenReference(), JmlMessages.INVALID_SIGNALS_CLAUSE, "");
        }
        JmlPredicate pred = sigClause.predOrNot();
        String var = varGen.freshPostVar();
        RacContext ctx = RacContext.createPositive();
        boolean isMethodCrosscutSpecChecking = AspectUtil.getInstance().isCrosscutSpecChecking(this.methodDecl);
        TransPostExpression2 trans =
                new TransPostExpression2(varGen, ctx, oldVarGen,
                        methodDecl.isStatic(), pred, null, typeDecl, "JMLExitExceptionalPostconditionError");
        this.combineSpecCases(xPostconditionForContext, trans.stmtAsString());
        if (isMethodCrosscutSpecChecking) {
            if (trans.stmtAsString().contains("this.")) {
                AspectUtil.getInstance().hasThisRef = true;
            }
        }
        if (oldExprs.containsKey(index)) {
            List currentExprsList = (List) oldExprs.get(index);
            currentExprsList.addAll(trans.oldExprs());
            oldExprs.put(index, currentExprsList);
        } else {
            oldExprs.put(index, trans.oldExprs());
        }
        if (oldExprsDecl.containsKey(index)) {
            List currentExprsDeclList = (List) oldExprsDecl.get(index);
            currentExprsDeclList.addAll(trans.oldVarDecl());
            oldExprsDecl.put(index, currentExprsDeclList);
        } else {
            oldExprsDecl.put(index, trans.oldVarDecl());
        }
        StringBuilder code = new StringBuilder("\n");
        if (preVar != null) {
            String quantifiers = this.getQuantifierInnerClasses(AspectUtil.changeThisOrSuperRefToAdviceRef(trans.stmtAsString(), typeDecl));
            if (!quantifiers.isEmpty()) {
                code.append("\t\t\t  ").append(quantifiers).append("\n");
            }
            String xPost = AspectUtil.changeThisOrSuperRefToAdviceRef(trans.stmtAsString(), typeDecl);
            code.append("\t\t\t  cute.Cute.Assert(").append(xPost).append(");\n");
        }
        return code.toString();
    }

    private String getQuantifierInnerClasses(String invPredicate) {
        StringBuffer result = new StringBuffer();
        result.append("");
        if (invPredicate.contains(CN_RAC_QUANTIFIER_ID)) {
            List ids = AspectUtil.getInstance().getQuantifierUniqueIDs();
            for (Iterator iterator = ids.iterator(); iterator.hasNext(); ) {
                String currentID = (String) iterator.next();
                if (invPredicate.contains(currentID)) {
                    result.append(AspectUtil.getInstance().getQuantifierInnerClassByID(currentID) + "\n");
                }
            }
        }
        return AspectUtil.changeThisOrSuperRefToAdviceRef(result.toString(), typeDecl);
    }

    /**
     * Composes the (implicit or explicit) <code>non_null</code> annotations of formal
     * parameters, if any, into a JML expression and return it.
     * If all parameters are nullable then,
     * the method returns <code>null</code>.
     * <p/>
     * <pre><jml>
     * ensures (* \result may be null *);
     * </jml></pre>
     */
    protected JExpression preNonNullAnnotations() {
        JExpression root = null;
        JFormalParameter[] params = methodDecl.parameters();
        for (int i = 0; i < params.length; i++) {
            if (params[i].isDeclaredNonNull()) { //NonNull()) {
                // build expression of the form: x != null
                TokenReference tref = params[i].getTokenReference();
                JExpression expr = new JEqualityExpression(tref, OPE_NE,
                        new JLocalVariableExpression(tref, params[i]),
                        new JNullLiteral(tref));

                // build rac predicate (for error reporting) and conjoin it
                expr = new RacPredicate(expr,
                        "non_null for parameter '" +
                                params[i].ident()
                                + "'");
                root = root == null ?
                        expr : new JConditionalAndExpression(tref, root, expr);
            }
        }
        //		if(root != null){
        //		System.err.println(root.toString());
        //		}
        return root;
    }

    /**
     * Returns an expression conjoinable to the normal postcondition,
     * that checks the <code>non_null</code> annotation of the method
     * declaration. If the method declaration is <code>nullable</code> then
     * <code>null</code> is returned.
     */
    protected /*@ nullable @*/ JExpression postNonNullAnnotation() {
        if (!methodDecl.isDeclaredNonNull()) { //NonNull() ) {
            return null;
        }
        // Return type declared non-null either explicitly or implicitly ...

        // build AST node for \result with typecheck information
        TokenReference tref = methodDecl.getTokenReference();
        JmlResultExpression rexpr = new JmlResultExpression(tref);
        rexpr.setType(methodDecl.returnType());

        // build expression of the form: \result != null
        JExpression eqexpr = new JEqualityExpression(tref, OPE_NE, rexpr,
                new JNullLiteral(tref));

        // build and return a RacPredicate for the error printing purpose
        // (see TransExpression.visitRacPredicate(RacPredicate)).
        return new RacPredicate(eqexpr, "non_null for result");
    }

    /**
     * @return true iff methodDecl has explicit spec cases at least
     * one of which is not a redundant spec case (e.g. imples_that
     * introduces a redundant spec case.
     */
    private boolean methodHasRealExplicitSpecs() {
        if (!methodDecl.hasSpecification())
            return false;
        //@ assert methodDecl.methodSpecification() != null;
        JmlSpecCase[] specCases = methodDecl.methodSpecification().specCases();
        return specCases != null && specCases.length > 0;
        // It would seem that all elements in specCases are
        // non-redundant, hence not need to inspec the content of this
        // array.
    }

    /**
     * Returns the name of the targe method declaration being
     * translated.
     */
    protected String methodName() {
        return methodDecl.ident();
    }

    // ----------------------------------------------------------------------
    // INNER CLASSES
    // ----------------------------------------------------------------------

    /**
     * A class for collecting all specification cases from a desugared
     * method specification. A <em>desugared method specification</em>
     * is a method specification that consists of only <em>general
     * behavior specification cases</em>.
     *
     * @author Yoonsik Cheon
     * @version $Revision: 1.68 $
     * @see DesugarSpec
     * @see org.jmlspecs.checker.JmlGenericSpecCase
     */
    protected static class SpecCaseCollector extends JmlAbstractVisitor
            implements JmlVisitor {

        /**
         * Constructs a new instance.
         * <p/>
         * <pre><jml>
         * requires mspec != null && (* mspec is desugared *);
         * </jml></pre>
         */
        protected SpecCaseCollector(JmlMethodSpecification mspec) {
            super();
            specCases = new ArrayList();
            if (mspec != null)
                mspec.accept(this);
        }

        public void visitJmlExtendingSpecification(
                JmlExtendingSpecification self) {
            JmlSpecCase[] specCases = self.specCases();
            if (specCases != null)
                for (int i = 0; i < specCases.length; i++)
                    specCases[i].accept(this);
        }

        public void visitJmlSpecification(JmlSpecification self) {
            JmlSpecCase specCases[] = self.specCases();
            if (specCases != null)
                for (int i = 0; i < specCases.length; i++) {
                    specCases[i].accept(this);
                }
        }

        public void visitJmlBehaviorSpec(JmlBehaviorSpec self) {
            specCases.add(new GeneralSpecCase(self.specCase()));
        }

        /**
         * Returns an iterator over all collected spec cases.
         * <p/>
         * <pre><jml>
         * ensures \result != null && (* each element of \result is
         * instanceof GeneralSpecCase *);
         * </jml></pre>
         */
        public Iterator iterator() {
            return specCases.iterator();
        }

        /**
         * List of desugared JmlGenericSpecCase.
         */
        private /*@ non_null @*/ List specCases;
    }

    /**
     * An abstract superclass for conjoining multiple specification
     * clauses, such as <code>requires</code> and <code>ensures</code>
     * clauses, in a specification case.
     *
     * @author Yoonsik Cheon
     * @version $Revision: 1.68 $
     */
    protected static abstract class SpecCase {
        protected SpecCase(JmlSpecBodyClause[] bc) {
            bodyClauses = bc;
            if (bodyClauses == null)
                bodyClauses = new JmlSpecBodyClause[0];
        }

        /**
         * Returns true if this spec case has any specification
         * variable declarations.
         */
        public abstract boolean hasSpecVarDecls();

        /**
         * Returns true if this spec case has the precondition
         * specified.
         */
        public abstract boolean hasPrecondition();

        /**
         * Returns true if this spec case has the normal
         * postcondition specified.
         */
        public boolean hasPostcondition() {
            for (int i = 0; i < bodyClauses.length; i++)
                if ((bodyClauses[i] instanceof JmlEnsuresClause) &&
                        isCheckable(bodyClauses[i]))
                    return true;
            return false;
        }

        /**
         * Returns true if this spec case has the postcondition.
         */
        public boolean hasExceptionalPostcondition() {
            for (int i = 0; i < bodyClauses.length; i++)
                if (isCheckable(bodyClauses[i]) &&
                        (bodyClauses[i] instanceof JmlSignalsClause ||
                                bodyClauses[i] instanceof JmlSignalsOnlyClause))
                    return true;
            return false;
        }

        /**
         * Returns the specification variable declarations of this
         * spec case.
         */
        public abstract JmlSpecVarDecl[] specVarDecls();

        /**
         * Returns the precondition of this spec case. If this spec
         * case has multiple <code>requires</code> clauses, the
         * clauses are conjoined.
         *
         * @see #conjoin(List)
         */
        public abstract JExpression precondition();

        /**
         * Returns the normal postcondition of this spec case. If
         * this spec case has multiple <code>ensures</code> clauses,
         * the clauses are conjoined.
         *
         * @see #conjoin(List)
         */
        public JExpression postcondition() {
            List l = new ArrayList();
            for (int i = 0; i < bodyClauses.length; i++) {
                if ((bodyClauses[i] instanceof JmlEnsuresClause)
                        && isCheckable(bodyClauses[i])) {
                    l.add(bodyClauses[i]);
                }
            }
            if (l.size() > 0)
                return conjoin(l);
            return null;
        }

        /**
         * Returns true if the given spec body clause is
         * checkable. The clause is checkable if it is not a redundant
         * specification or the command line option "noredundancy" is
         * not turned on.
         */
        protected boolean isCheckable(JmlSpecBodyClause clause) {
            return !clause.isRedundantly() || !Main.aRacOptions.noredundancy();
        }

        /**
         * Returns the exceptional postcondition of this spec
         * case. If this spec case has multiple <code>signals</code>
         * clauses, the clauses are conjoined. If this spec case has a
         * signals_only clause, it is first desugared into a signals
         * clause.
         * <p/>
         * <pre><jml>
         * ensures \result != null ==> \result.length > 0;
         * </jml></pre>
         *
         * @see #conjoin(List)
         */
        public JmlSignalsClause[] exceptionalPostcondition() {
            List l = new ArrayList();

            for (int i = 0; i < bodyClauses.length; i++) {
                if (!isCheckable(bodyClauses[i])) {
                    continue;
                }
                if (bodyClauses[i] instanceof JmlSignalsClause) {
                    JmlSignalsClause sig = (JmlSignalsClause) bodyClauses[i];
                    exceptionsInSignalsClauses.add(sig.type());
                    if (sig.ident() != null) {
                        if (sig.ident().equals("jml$e")) {
                            JmlRacGenerator.fail(sig.getTokenReference(), JmlMessages.INVALID_SIGNALS_CLAUSE_VAR_IDENT, "");
                        }
                    }
                    AspectUtil.getInstance().appendExceptionInSignalsClauseInCompilationUnit(sig.type());
                    l.add(bodyClauses[i]);
                } else if (bodyClauses[i] instanceof JmlSignalsOnlyClause) {
                    JmlSignalsOnlyClause sig = (JmlSignalsOnlyClause) bodyClauses[i];
                    if (!sig.isNothing()) {
                        CClassType[] exceptions = sig.exceptions();
                        for (int j = 0; j < exceptions.length; j++) {
                            exceptionsInSignalsClauses.add(exceptions[j].getErasure());
                            AspectUtil.getInstance().appendExceptionInSignalsClauseInCompilationUnit(exceptions[j].getErasure());
                        }
                    }
                    l.add(desugar((JmlSignalsOnlyClause) bodyClauses[i]));
                }
            }

            if (l.size() > 0) {
                JmlSignalsClause[] sc = new JmlSignalsClause[l.size()];
                l.toArray(sc);
                return sc;
            }
            return null;
        }

        public JmlAssignableClause[] assignable() {
            List l = new ArrayList();

            for (int i = 0; i < bodyClauses.length; i++) {
                if (!isCheckable(bodyClauses[i])) {
                    continue;
                }
                if (bodyClauses[i] instanceof JmlAssignableClause) {
                    l.add(bodyClauses[i]);
                }
            }

            if (l.size() > 0) {
                JmlAssignableClause[] sc = new JmlAssignableClause[l.size()];
                l.toArray(sc);
                return sc;
            }
            return null;
        }

        /**
         * Desugars a signals_only clause into a signals clause. A
         * signals_only clause of the form:
         * <p/>
         * <pre>
         *  signals_only \nothing;
         * </pre>
         * <p/>
         * is desugared into the following signals clause:
         * <p/>
         * <pre>
         *  signals (java.lang.Exception e) false;
         * </pre>
         * <p/>
         * Furthermore, a signals_only clause of the form
         * <p/>
         * <pre>
         *  signals_only E1, E2, ..., En;
         * </pre>
         * <p/>
         * is desugared into the following signals clause:
         * <p/>
         * <pre>
         *  signals (java.lang.Exception e)
         *       e instanceof E1
         *    || e instanceof E2
         *       ...
         *    || e instanceof En;
         * </pre>
         */
        private  /*@ non_null @*/ JmlSignalsClause desugar(
                /*@ non_null @*/ JmlSignalsOnlyClause sig) {

            TokenReference tref = sig.getTokenReference();
            if (sig.isNothing()) {
                JExpression expr = new JBooleanLiteral(tref, false);
                JmlPredicate pred
                        = new JmlPredicate(new JmlSpecExpression(expr));
                return new JmlSignalsClause(tref,
                        sig.isRedundantly(),
                        CStdType.Exception,
                        "jml$e",
                        pred,
                        false);
            }

            CClassType[] exceptions = sig.exceptions();
            //@ assume exceptions.length > 0;

            JExpression expr = null;
            for (int i = 0; i < exceptions.length; i++) {
                if (!isValidSignalsClause(exceptions[i].getCClass())) {
                    JmlRacGenerator.fail(sig.getTokenReference(), JmlMessages.INVALID_SIGNALS_ONLY_CLAUSE, "");
                }
                JVariableDefinition var = new JVariableDefinition(
                        tref, 0, CStdType.Exception, "jml$e", null);
                JLocalVariableExpression varExpr =
                        new JLocalVariableExpression(tref, var);
                JExpression inst = new JInstanceofExpression(
                        tref, varExpr, exceptions[i]);
                expr = (expr == null) ? inst :
                        new JConditionalOrExpression(tref, expr, inst);
            }

            JmlPredicate pred = new JmlPredicate(new JmlSpecExpression(expr));
            return new JmlSignalsClause(tref,
                    sig.isRedundantly(),
                    CStdType.Exception,
                    "jml$e",
                    pred,
                    false);
        }

        /**
         * Returns a new conjoined expression made out of predicates
         * of the given specification clauses. A null is returned if
         * there is nothing to be conjoined in the given list of
         * specification clauses. A specification clause corresponding
         * to <code>\not_specified</code> is desugared into true.
         * <p/>
         * <pre><jml>
         * requires clauses != null &&
         *   (\forall Object o; clauses.contains(o);
         *     (o instanceof JmlRequiresClause) ||
         *     (o instanceof JmlEnsuresClause));
         * </jml></pre>
         */
        protected static JExpression conjoin(List clauses) {
            JExpression left = null;
            Iterator iter = clauses.iterator();
            JmlPredicateClause notSpecified = null;
            while (iter.hasNext()) {
                JmlPredicateClause c = (JmlPredicateClause) iter.next();
                if (!c.isNotSpecified()) {
                    RacPredicate p = new RacPredicate(c.predOrNot());
                    if (left == null)
                        left = p;
                    else
                        left = new JConditionalAndExpression(org.multijava.util.compiler.TokenReference.NO_REF,
                                left, p);
                } else if (notSpecified == null) {
                    notSpecified = c;
                }
            }

            // desugar \not_specified as true; 
            // see testcase AlsoAndLightweight.java
            if (left == null && notSpecified != null) {
                return new JBooleanLiteral(
                        notSpecified.getTokenReference(), true);
            }
            return left;
        }

        protected /*@ non_null @*/ JmlSpecBodyClause[] bodyClauses;
    }

    /**
     * A concrete wrapper class to <code>JmlGeneralSpecCase</code> for
     * conjoining multiple specification clauses in a specification
     * case.
     *
     * @author Yoonsik Cheon
     * @version $Revision: 1.68 $
     * @see org.jmlspecs.checker.JmlGeneralSpecCase
     */
    protected static class GeneralSpecCase extends SpecCase {
        /**
         * Constructs a new instance.
         * <p/>
         * <pre><jml>
         * requires spec != null && (* spec is desugared *);
         * </jml></pre>
         */
        public GeneralSpecCase(JmlGeneralSpecCase spec) {
            super((spec.hasSpecBody() && spec.specBody().isSpecClauses()) ?
                    spec.specBody().specClauses() : null);
            this.spec = spec;
        }

        /**
         * Returns true if this spec case has any specification
         * variable declarations.
         */
        public boolean hasSpecVarDecls() {
            return spec.hasSpecVarDecls();
        }

        /**
         * Returns true if this spec case has the precondition
         * specified.
         */
        public boolean hasPrecondition() {
            if (spec.hasSpecHeader()) {
                JmlRequiresClause[] clauses = spec.specHeader();
                for (int i = 0; i < clauses.length; i++) {
                    if (isCheckable(clauses[i]))
                        return true;
                }
            }
            return false;
        }

        /**
         * Returns the specification variable declarations of this
         * spec case.
         */
        public JmlSpecVarDecl[] specVarDecls() {
            return spec.specVarDecls();
        }

        /**
         * Returns the precondition of this spec case. If this spec
         * case has multiple <code>requires</code> clauses, the
         * clauses are conjoined.
         */
        public JExpression precondition() {
            if (spec.hasSpecHeader()) {
                JmlRequiresClause[] clauses = spec.specHeader();
                List l = new ArrayList();
                for (int i = 0; i < clauses.length; i++) {
                    if (clauses[i].hasSamePredicate())
                        continue;
                    if (isCheckable(clauses[i]))
                        l.add(clauses[i]);
                }
                if (l.size() > 0)
                    return conjoin(l);
            }
            return null;
        }

        /**
         * The spec case whose specification clauses to be conjoined.
         */
        private /*@ non_null @*/ JmlGeneralSpecCase spec;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /**
     * Target type declaration whose methods are to be translated.
     * <p/>
     * <pre><jml>
     * protected invariant typeDecl != null;
     * </jml></pre>
     */
    protected final /*@ spec_public @*/ JmlTypeDeclaration typeDecl;


    /**
     * target method to be transformed.
     * <p/>
     * <pre><jml>
     * protected invariant methodDecl != null ==>
     *   typeDecl.methods().contains(methodDecl);
     * </jml></pre>
     */
    protected /*@ spec_public @*/ JmlMethodDeclaration methodDecl;

    /**
     * newly created fields (as the result of translation) that
     * need be added to the target class, e.g., old and precondition
     * variables
     */
    protected /*@ spec_public non_null @*/ List newFields;

    /**
     * newly created methods (as the result of translation) that
     * need be added to the target class
     */
    protected /*@ spec_public non_null @*/ List newMethods;

    /**
     * desugared specification of the target method to be translated
     */
    protected /*@ spec_public @*/ JmlMethodSpecification desugaredSpec;

    /**
     * for generating fresh variables needed in the generated Java code
     */
    protected /*@ non_null @*/ VarGenerator varGen;

    static List<CType> exceptionsInSignalsClauses;
}

