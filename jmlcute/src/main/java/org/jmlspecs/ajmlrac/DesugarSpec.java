/*
 * Copyright (C) 2001 - 2003 Iowa State University
 *
 * This file is part of JML
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
 * $Id: DesugarSpec.java,v 1.22 2005/09/16 05:59:48 cruby Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.*;
import org.jmlspecs.util.AspectUtil;
import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import java.util.*;

/**
 * A JML visitor class for desugaring method specifications. In the
 * desugared form, a generic specification, a normal behavior
 * specification and a exceptional specification are all translated
 * into a (general form of) behavior specification. A case-analysis
 * specification, known as <em>specification cases</em>, and a nested
 * specification are also desugared. The desugaring does not produce a
 * completely desugared method specification, but a partial form
 * sufficient for the further processing by the runtime assertion
 * checker.
 *
 * <p>In the desugared specification, each specification case is
 * translated into a general behavior specification case. If
 * necessary, a default specification body clause such as
 * <code>ensures</code> clause and <code>signals</code> clause is
 * added. A specification cases specification is desugared by copying
 * specificification variable declarations and specification headers
 * into each specification case. A nested specification is desugared
 * by unfolding the nesting. For example, the following specification:
 * 
 * <pre>
 *  also requires p1; {| ensures p2; also ensures p3; |}
 *  also behavior ensures p4;
 *  also normal_behavior ensures p5;
 *  also exceptional_behavior signals (E e) p6;
 * </pre>
 *
 * is desugared into: 
 *
 * <pre>
 *  also behavior requires p1; ensures p2;
 *  also behavior requires p1; ensures p3;
 *  also behavior ensures p4;
 *  also behavior ensures p5; signals (Exception e) false;
 *  also behavior signals (E e) p6; ensures false;
 * </pre>
 */
public class DesugarSpec extends JmlAbstractVisitor 
    implements JmlVisitor {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /** Constructs a new instance. */
    public DesugarSpec() {
    }

    // ----------------------------------------------------------------------
    // DESUGARING
    // ----------------------------------------------------------------------

    /** Returns a desugared specification of the given method
     * specification.
     *
     * @param mspec the method specification to be desugared
     * @param exceptions exceptions that the target method may throw.
     * @return the desugared method specification
     * @see #visitJmlSpecification(JmlSpecification)
     */
    public /*@ non_null @*/ JmlMethodSpecification perform(
        /*@ non_null @*/ JmlMethodSpecification mspec,
        CClassType[] exceptions) 
    {

	//Debug.initialize(false);
	//Debug.setPrefix("Desugar");

        this.exceptions = exceptions;

        // for passing arguments and results between visitor methods
	resultStack = new Stack();

	mspec.accept(this);

	//Debug.initialize(false);
       
        // nothing need be desugared?
        if (resultStack.isEmpty())
            return mspec;
        else 
            return (JmlMethodSpecification) resultStack.pop();
    }

    // ----------------------------------------------------------------------
    // VISITORS
    // ----------------------------------------------------------------------

    /** Desugars the given JML specification. In the desugared
     * specification, each specification case is translated into a
     * general behavior specification case. A default specification
     * body clause such as <code>ensures</code> clause and
     * <code>signals</code> clause is added if necessary. A
     * specification cases specification is desugared by copying
     * specificification variable declarations and specification
     * headers into each specification case. A nested specification is
     * desugared by unfolding the nesting. For example, the following
     * specification:
     * 
     * <pre>
     *  also requires p1; {| ensures p2; also ensures p3; |}
     *  also behavior ensures p4;
     *  also normal_behavior ensures p5;
     *  also exceptional_behavior signals (E e) p6;
     * </pre>
     *
     * is desugared into: 
     *
     * <pre>
     *  also behavior requires p1; ensures p2;
     *  also behavior requires p1; ensures p3;
     *  also behavior ensures p4;
     *  also behavior ensures p5; signals (Exception e) false;
     *  also behavior signals (E e) p6; ensures false;
     * </pre>
     *
     * Both the subclassing contract and redundant specifications are not
     * desugared.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     *
     */
    public void visitJmlSpecification( JmlSpecification self ) 
    {
	//Debug.msg("In JmlSpecification");
	visitSpecification(self);
    }

    /**
     * Desugars a JML specification or an OR-extending specification.
     *
     * <pre><jml>
     * requires self != null && resultStack != null;
     * requires (self instanceof JmlSpecification) ||
     *    (* self is an OR-extending specification *);
     * assignable resultStack;
     * ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */    
    private void visitSpecification( JmlSpecification self ) 
    {
	JmlSpecCase[] newSpecCases = null;
	if (self.hasSpecCases()) {
	    JmlSpecCase[] specCases = self.specCases();
	    List l = new ArrayList();

            // desugar each spec case and store it into the list l
	    for (int i = 0; i < specCases.length; i++) {
                // ignore model program specifications
                if (specCases[i].isCodeSpec())
		    // !FIXME! need to handle \same first
                    continue;
                if (specCases[i] instanceof JmlCodeContract)
                    continue;
                if (specCases[i] instanceof JmlModelProgram)
                    continue;

                // desugar the i-th spec case
                specCases[i].accept(this);
                JmlSpecCase r = (JmlSpecCase) GET_RESULT();

                // transform generic spec case into behavior spec case
                if (r instanceof JmlGenericSpecCase) {
                    r = new JmlBehaviorSpec(specCases[i].getTokenReference(),
                                            0, (JmlGenericSpecCase) r);
                }
                
                // desugar the top-level nesting and add a default
                // requires clause if the original spec case is behavioral one.
                JmlBehaviorSpec bspec = (JmlBehaviorSpec) r;
                if (bspec.isNestedSpec()) {
                    JmlGenericSpecCase[] c = (JmlGenericSpecCase[])
                        bspec.specCase().specBody().specCases();
                    for (int j = 0; j < c.length; j++) {
                        JmlBehaviorSpec bs = new JmlBehaviorSpec(
                            c[j].getTokenReference(),
                            bspec.privacy(), 
                            c[j]);
                        l.add(addDefaultRequiresClause(bs));
                    }
                } else {
                    l.add(addDefaultRequiresClause(bspec));
                }
	    } // for
	    
	    newSpecCases = new JmlBehaviorSpec[l.size()];
	    l.toArray(newSpecCases);
	}

        // build a JmlSpecification out of desugared spec cases
	Object result = new JmlSpecification(
	    self.getTokenReference(),
	    newSpecCases,
	    self.redundantSpec());
	
        // turn it into JmlSpecification if necessary
	if (self instanceof JmlExtendingSpecification) {
	    result = new JmlExtendingSpecification((JmlSpecification)result);
	}
	RETURN_RESULT(result);
    }

    /** 
     * Adds a default <code>requires</code> clause to the given
     * behaviorSpec, <code>bs</code>, and returns it.
     */
    private JmlBehaviorSpec addDefaultRequiresClause(JmlBehaviorSpec bs) {
        JmlGeneralSpecCase sc = bs.specCase();
        if (!sc.hasNonRedundantRequiresClause()) {
           sc.addRequiresClause(defaultRequiresClause(bs.getTokenReference()));
        }
        return bs;
    }

    /** Desugar an extending specification. In the desugared 
     * specification, each conjoinable specification is translated into
     * a corresponding behavior conjoinable specification, if necssary,
     * with a default specification body clause added. For example, the
     * method specification of:
     * 
     * <pre>
     *  and ensures p1; 
     *  and behavior ensures p2;
     *  and normal_behavior ensures p3;
     *  and exceptional_behavior signals (E e) p4;
     * </pre>
     *
     * is desugared into: 
     *
     * <pre>
     *  and behavior ensures p1;
     *  and behavior ensures p2;
     *  and behavior ensures p3; signals (Exception e) false;
     *  and behavior signals (E e) p4; ensures false;
     * </pre>
     *
     * Redundant specifications are not desugared.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlExtendingSpecification( 
       JmlExtendingSpecification self ) 
    {
	Debug.msg("In JmlExtendingSpecification");

	// is an OR-extendsion?
	if (self.hasSpecCases()) {
	    visitSpecification(self);
	    return;
	}
    }

    /** Desugars a behavior specification.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlBehaviorSpec( JmlBehaviorSpec self ) 
    {
	visitHeavyweightSpec(self);
    }

    /** Desugars a normal behavior specification.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre> 
     */
    public void visitJmlNormalBehaviorSpec( JmlNormalBehaviorSpec self ) 
    {
	visitHeavyweightSpec(self);
    }

    /** Desugars an exceptional behavior specification.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlExceptionalBehaviorSpec( 
       JmlExceptionalBehaviorSpec self ) 
    {
	visitHeavyweightSpec(self);
    }

    /** Desugars a generic specification case.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlGenericSpecCase( JmlGenericSpecCase self ) 
    {
	visitSpecCase(self);
    }

    /** Desugars a generic specification body. 
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlGenericSpecBody( JmlGenericSpecBody self ) 
    {
        JmlSpecBodyClause defaultBC = null;

        // default signals for lightweight specifications
        if (!heavyweight && self.isSpecClauses()) {
	    JmlSpecBodyClause[] nb = self.specClauses();
            boolean hasSignals = false;
            for (int i = 0; i < nb.length; i++) {
                if ((nb[i] instanceof JmlSignalsClause) 
                    || (nb[i] instanceof JmlSignalsOnlyClause)) { 
                    hasSignals = true;
                    break;
                }
            }
            if (!hasSignals) {
                defaultBC = defaultSignalsClause(self.getTokenReference(),
                                                 exceptions);
            }
        }

	visitSpecBody(self, defaultBC);
    }

   /** Desugars a normal specification case. 
    *
    * <pre><jml>
    * also
    *   requires self != null && resultStack != null;
    *   assignable resultStack;
    *   ensures resultStack.size() == \old(resultStack.size() + 1);
    * </jml></pre>
    */
    public void visitJmlNormalSpecCase( JmlNormalSpecCase self ) 
    {
	visitSpecCase(self);
    }


    /** Desugars a normal specification body. 
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlNormalSpecBody( JmlNormalSpecBody self ) 
    {
	visitSpecBody(self, defaultSignalsClause(self.getTokenReference()));
    }


    /** Desugars an exceptional specification case. 
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    public void visitJmlExceptionalSpecCase( JmlExceptionalSpecCase self ) 
    {
	visitSpecCase(self);
    }

    /** Desugars an exceptional specification body.
     *
     * <pre><jml>
     * also
     *   requires self != null && resultStack != null;
     *   assignable resultStack;
     *   ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>        
     */
    public void visitJmlExceptionalSpecBody( JmlExceptionalSpecBody self ) 
    {
	visitSpecBody(self, defaultEnsuresClause(self.getTokenReference()));
    }

    // ----------------------------------------------------------------------
    // PRIVATE HELPER METHODS
    // ----------------------------------------------------------------------

    /** Desugars a general/normal/exceptional behavior specification. 
     *
     * <pre><jml>
     * requires self != null && resultStack != null;
     * assignable resultStack;
     * assignable_redundantly heavyweight;
     * ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>        
     */
    private void visitHeavyweightSpec( JmlHeavyweightSpec self )
    {
	JmlGeneralSpecCase specCase = self.specCase();
        heavyweight = true;
	specCase.accept(this);
        heavyweight = false;
	specCase = (JmlGeneralSpecCase) GET_RESULT();
	JmlBehaviorSpec result = new JmlBehaviorSpec(
	   self.getTokenReference(), self.privacy(), specCase);
	RETURN_RESULT(result);
    }

    /** Returns a default requires clause for an behavior spec case.
     *
     * <pre><jml>
     * requires where != null;
     * ensures \result != null;
     * </jml></pre> 
     */
    protected JmlRequiresClause defaultRequiresClause(TokenReference where) 
    {
	JmlPredicate pred 
	    = new JmlPredicate(new JmlSpecExpression(
				         new JBooleanLiteral(where, true)));
	return new JmlRequiresClause(where, false, pred);
    }

    /** 
     * Returns a default signals clause for a normal specification.
     * The returned signals clause has the form: <code>signals
     * (Exception e) false</code>.
     *
     * <pre><jml>
     * requires where != null;
     * ensures \result != null;
     * </jml></pre>
     */
    private JmlSignalsClause defaultSignalsClause(TokenReference where) {
	// !FIXME! define a constant for "jml$e"
	JmlPredicate pred 
	    = new JmlPredicate(new JmlSpecExpression(
				         new JBooleanLiteral(where, false)));
	AspectUtil.getInstance().appendDefaultSignalsClauseTokenRefereces(pred.getTokenReference().toString());
	return new JmlSignalsClause(where, false, CStdType.Exception,
				    "jml$ex", pred, false);
    }

    /** 
     * Returns a default signals clause for a lightweight
     * specification whose method may throw the given exceptions.  The
     * returned signals clause has the form: 
     *
     * <pre>
     *  signals (Throwable e) e instanceof E1 || ... || e instanceof En;
     * </pre>
     */
    private /*@ non_null@*/ JmlSignalsClause defaultSignalsClause(
        /*@ non_null @*/ TokenReference where,
        CClassType[] exceptions) {

    	// not anymore... [[[hemr]]]
//        if (exceptions == null || exceptions.length == 0) {
//            return defaultSignalsClause(where);
//        }
        
        // new one
        if (exceptions == null || exceptions.length == 0) {
    		return defaultSignalsClauseAsRuntimeException(where);
    	}

        JExpression expr = null;
        for (int i = 0; i < exceptions.length; i++) {
            JVariableDefinition var = new JVariableDefinition(
                where, 0, CStdType.Throwable, "jml$ex", null);
            JLocalVariableExpression varExpr =
                new JLocalVariableExpression(where, var);
            JExpression inst = new JInstanceofExpression(
                where, varExpr, exceptions[i]);
            expr = (expr == null) ? inst :
                new JConditionalOrExpression(where, expr, inst);
            
         // adding RuntimeException to the end of exception list --- [[[hemr]]]
            if((i+1) == exceptions.length){
            	 var = new JVariableDefinition(
                         where, 0, CStdType.Throwable, "jml$ex", null);
                     varExpr =
                         new JLocalVariableExpression(where, var);
                     inst = new JInstanceofExpression(
                         where, varExpr, CStdType.RuntimeException);
                     expr = (expr == null) ? inst :
                         new JConditionalOrExpression(where, expr, inst);
            }
        }

        JmlPredicate pred 
	    = new JmlPredicate(new JmlSpecExpression(expr));
        return new JmlSignalsClause(where, 
                                    false,
                                    CStdType.Throwable,
                                    "jml$ex",
                                    pred,
                                    false);
    }
    
    protected /*@ non_null@*/ JmlSignalsClause defaultSignalsClause2(
            /*@ non_null @*/ TokenReference where,
            CClassType[] exceptions) {

    	// not anymore... [[[hemr]]]
//            if (exceptions == null || exceptions.length == 0) {
//                return defaultSignalsClause(where);
//            }
    	
    	// new one
    	if (exceptions == null || exceptions.length == 0) {
    		return defaultSignalsClauseAsRuntimeException(where);
    	}

            JExpression expr = null;
            for (int i = 0; i < exceptions.length; i++) {
                JVariableDefinition var;
                JLocalVariableExpression varExpr;
                JExpression inst;
                if (TransMethod.isValidSignalsClause(exceptions[i].getCClass())) {
					var = new JVariableDefinition(where, 0, CStdType.Throwable,
							"jml$ex", null);
					varExpr = new JLocalVariableExpression(where, var);
					inst = new JInstanceofExpression(where, varExpr,
							exceptions[i]);
					expr = (expr == null) ? inst
							: new JConditionalOrExpression(where, expr, inst);
				}
				// adding RuntimeException to the end of exception list --- [[[hemr]]]
                if((i+1) == exceptions.length){
                	 var = new JVariableDefinition(
                             where, 0, CStdType.Throwable, "jml$ex", null);
                         varExpr =
                             new JLocalVariableExpression(where, var);
                         inst = new JInstanceofExpression(
                             where, varExpr, CStdType.RuntimeException);
                         expr = (expr == null) ? inst :
                             new JConditionalOrExpression(where, expr, inst);
                }
            }

            JmlPredicate pred 
    	    = new JmlPredicate(new JmlSpecExpression(expr));
            return new JmlSignalsClause(where, 
                                        false,
                                        CStdType.Exception,
                                        "jml$ex",
                                        pred,
                                        false);
        }
    
    /** 
     * Returns a default signals clause for a normal specification.
     * The returned signals clause has the form: <code>signals
     * (RuntimeException e) true</code>.
     *
     * <pre><jml>
     * requires where != null;
     * ensures \result != null;
     * </jml></pre>
     */
    private JmlSignalsClause defaultSignalsClauseAsRuntimeException(TokenReference where) {
	JmlPredicate pred 
	    = new JmlPredicate(new JmlSpecExpression(
				         new JBooleanLiteral(where, true)));
	AspectUtil.getInstance().appendDefaultSignalsClauseTokenRefereces(pred.getTokenReference().toString());
	return new JmlSignalsClause(where, false, CStdType.RuntimeException,
				    "jml$ex", pred, false);
    }

    /** Returns a default ensures clause for an exceptional specification. 
     *
     * <pre><jml>
     * requires where != null;
     * ensures \result != null;
     * </jml></pre> 
     */
    protected JmlEnsuresClause defaultEnsuresClause(TokenReference where) 
    {
	JmlPredicate pred 
	    = new JmlPredicate(new JmlSpecExpression(
				         new JBooleanLiteral(where, false)));
	AspectUtil.getInstance().appendDefaultEnsuresClauseTokenRefereces(pred.getTokenReference().toString());
	return new JmlEnsuresClause(where, false, pred);
    }

    /** Desugars a specification case (general, normal, exceptional). 
     * <pre><jml>
     * requires self != null && resultStack != null;
     * assignable resultStack;
     * ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>    
     */
    private void visitSpecCase( JmlGeneralSpecCase self ) 
    {
	// If self has no spec body, throw in a default spec body clause.
	if (!self.hasSpecBody()) {

	    JmlSpecBodyClause[] bc = new JmlSpecBodyClause[1];
            if (!heavyweight && (self instanceof JmlGenericSpecCase)) {
                // for a lightweight spec case, add a signals clause
                // by taking into account of the throws clause.
                bc[0] = defaultSignalsClause(self.getTokenReference(),
                                             exceptions);
            } else if ((self instanceof JmlGenericSpecCase)
                       || (self instanceof JmlNormalSpecCase)) {
		bc[0] = defaultSignalsClause(self.getTokenReference());
	    } else { // JmlExceptionalSpecCase
		bc[0] = defaultEnsuresClause(self.getTokenReference());
	    }
	    
	    JmlGenericSpecCase result = 
		new JmlGenericSpecCase( self.getTokenReference(), 
                self.specVarDecls(), self.specHeader(), 
		new JmlGenericSpecBody(bc));
	    RETURN_RESULT(result);
	    return;
	}

	// desugar the spec body
	self.specBody().accept(this);

	// make a new generic spec case for building behavior spec later
	JmlSpecBody specBody = (JmlSpecBody) GET_RESULT();
	JmlSpecVarDecl[] specVarDecls = self.specVarDecls();
	JmlRequiresClause[] specHeader = self.specHeader();
	JmlGenericSpecCase result = null;

	if (!specBody.isSpecCases()) {
	    // done if body is not spec cases
	    result = new JmlGenericSpecCase( self.getTokenReference(), 
                specVarDecls, specHeader, (JmlGenericSpecBody) specBody);
	} else {
	    // desugar spec cases, i.e., copy spec var and spec header
	    // into each spec case
	    JmlGenericSpecCase[] specCases
		= (JmlGenericSpecCase[])specBody.specCases();
	    JmlGenericSpecCase[] nspecCases 
		= new JmlGenericSpecCase[specCases.length];
	    for (int i = 0; i < specCases.length; i++) {
		nspecCases[i] = add(specCases[i], specVarDecls, specHeader);
	    }
	    result = new JmlGenericSpecCase( self.getTokenReference(), 
		null, null, new JmlGenericSpecBody(nspecCases));
	}

	RETURN_RESULT(result);
    }

    /** Desugars a specification body (general, normal, exceptional). 
     * <pre><jml>
     * requires self != null && resultStack != null;
     * assignable resultStack;
     * ensures resultStack.size() == \old(resultStack.size() + 1);
     * </jml></pre>
     */
    private void visitSpecBody( JmlSpecBody self, JmlSpecBodyClause body ) 
    {
	//@ assert (* self is either specClauses or specCases *);
	if (self.isSpecClauses()) {
	    JmlSpecBodyClause[] nb = null;
	    if (body == null){
		nb = self.specClauses();
	    } else {
		// add the given (default) body clause into spec body
		JmlSpecBodyClause[] ob = self.specClauses();
		nb = new JmlSpecBodyClause[ob.length + 1];
		System.arraycopy(ob, 0, nb, 0, ob.length);
		nb[ob.length] = body;
	    }
	    RETURN_RESULT(new JmlGenericSpecBody(nb));
	}

	if (self.isSpecCases()) {
	    // unfold the nesting, i.e., make it flat spec
	    JmlGeneralSpecCase[] c = self.specCases();
	    List l = new ArrayList();
	    for (int i = 0; i < c.length; i++) {
		c[i].accept(this);
		JmlGenericSpecCase r = (JmlGenericSpecCase)GET_RESULT();
		if (r.hasSpecBody() && r.specBody().isSpecCases())
		    l.addAll(Arrays.asList(r.specBody().specCases()));
		else
		    l.add(r);
	    }
	    JmlGenericSpecCase[] r = new JmlGenericSpecCase[l.size()];
	    l.toArray(r);
	    RETURN_RESULT(new JmlGenericSpecBody(r));
	}
    }

    /** Adds the given spec var decls, <code>specVarDecls</code>, and
     * spec header, <code>specHeader</code>, to the spec case,
     * <code>specCase</code>. */
    private JmlGenericSpecCase add(JmlGenericSpecCase specCase,
				   JmlSpecVarDecl[] specVarDecls,
				   JmlRequiresClause[] specHeader)
    {
	JmlSpecVarDecl[] v = specCase.specVarDecls();
	JmlSpecVarDecl[] nv = null;
	if (specVarDecls == null)
	    nv = v;
	else if (v == null)
	    nv = specVarDecls;
	else {
	    List l = new ArrayList();
	    l.addAll(Arrays.asList(specVarDecls));
	    l.addAll(Arrays.asList(v));
	    nv = new JmlSpecVarDecl[l.size()];
	    l.toArray(nv);
	}

	JmlRequiresClause[] h = specCase.specHeader();	
	JmlRequiresClause[] nh = null;
	if (specHeader == null)
	    nh = h;
	else if (h == null)
	    nh = specHeader;
	else {
	    List l = new ArrayList();
	    l.addAll(Arrays.asList(specHeader));
	    l.addAll(Arrays.asList(h));
	    nh = new JmlRequiresClause[l.size()];
	    l.toArray(nh);
	}

	return new JmlGenericSpecCase(specCase.getTokenReference(),
	   nv, nh, (JmlGenericSpecBody)specCase.specBody());
    }

    /** Pops and returns the top element of the result stack. 
     *
     * <pre><jml>
     * requires resultStack != null;
     * assignable resultStack;
     * ensures resultStack != null;
     * </jml></pre>
     */
    private Object GET_RESULT() 
    {
	return resultStack.pop();
    }

    /** Pushes the argument to the result stack. 
     * <pre><jml>
     * requires obj != null && resultStack != null;
     * assignable resultStack;
     * ensures resultStack != null;
     * </jml></pre>
     */
    private void RETURN_RESULT(Object obj) {
	resultStack.push(obj);
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    /** for passing results (return values) between visitor methods. 
     * @see #GET_RESULT()
     * @see #RETURN_RESULT(Object) */
    private /*@ spec_public @*/ Stack resultStack;

    /** Exceptions that the target method may throw. */
    private CClassType[] exceptions;

    /** True iff the current specification being desugared is
     * heavyweight. */
    private /*@ spec_public @*/ boolean heavyweight; //@ in resultStack;
}

