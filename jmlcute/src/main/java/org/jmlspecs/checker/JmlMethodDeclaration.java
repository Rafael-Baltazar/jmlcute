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
 * $Id: JmlMethodDeclaration.java,v 1.101 2007/04/18 23:04:37 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.jmlspecs.util.AspectUtil;
import org.jmlspecs.util.QDoxUtil;
import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CAbstractMethodSet;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMember;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodContextType;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.CSourceMethod;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.CUniverseRep;
import org.multijava.mjc.CVariableInfoTable;
import org.multijava.mjc.CodeSequence;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JMethodDeclarationType;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.MemberAccess;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.Utils;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

import com.thoughtworks.qdox.model.JavaMethod;

/**
 * JmlMethodDeclaration.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.101 $
 */

public class JmlMethodDeclaration extends JmlMemberDeclaration 
    implements JMethodDeclarationType
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    
    protected JmlMethodDeclaration( TokenReference where, 
				    /*@ nullable @*/ JmlMethodSpecification methodSpecification,
				    JMethodDeclaration delegee ) {
	super( where, delegee );
	this.methodSpecification = methodSpecification;
	this.delegee = delegee;
    }
    
    public static JmlMethodDeclaration 
	makeInstance( TokenReference where, long modifiers,
                      CTypeVariable[] typevariables, CType returnType,
		      String ident, JFormalParameter[] parameters,
		      CClassType[] exceptions, JBlock body,
		      JavadocComment javadoc, JavaStyleComment[] comments,
		      /*@ nullable @*/ JmlMethodSpecification methodSpecification ) {
	JMethodDeclaration delegee = 
	    new JMethodDeclarationWrapper(where, modifiers,
                                          typevariables, returnType, 
					  ident, parameters, exceptions, 
					  body, javadoc, comments );

	return new JmlMethodDeclaration( where, methodSpecification, 
					 delegee );
    }
						     
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /**
     * Indicates whether this method declaration has a body.  
     */
    public /*@ pure @*/ boolean hasBody() { 
	return delegee.hasBody();
    }

    /**
     * Returns the method declaration in the refinement chain that has a 
     * body. 
     */
    public JmlMethodDeclaration findDeclWithBody() {
	if (hasBody()) {
	    return this;
	} else {
	    JmlMemberDeclaration refMeth = this.getRefinedMember();
	    return ( !(refMeth instanceof JmlMethodDeclaration) ? 
		     null 
		     : ((JmlMethodDeclaration)refMeth).findDeclWithBody() );
	}
    }

    /**
     * Indicates whether the method declaration represented by this
     * has an explicit specification.  */
    public /*@ pure @*/ boolean hasSpecification() {
	JmlMethodSpecification methodSpecification = methodSpecification();
	return methodSpecification != null;
    }

    public /*@ pure nullable @*/ JmlMethodSpecification methodSpecification() {
	return methodSpecification;
    }

    public /*@ pure @*/ JFormalParameter[] parameters() {
	return delegee.parameters();
    }

    public void setParameters( JFormalParameter[] parameters ) {
	delegee.setParameters( parameters );
    }

    public /*@ pure @*/ CTypeVariable[] typevariables() {
        return delegee.typevariables();
    }

    /**
     * Adds an additional formal parameter to this method, appending
     * it to the end of the existing parameter list.  
     *
     * <pre><jml>
     * also
     *   requires param != null;
     * </jml></pre>
     */
    public void addParameter( JFormalParameter param ) {
	delegee.addParameter(param);
    }

    public /*@ pure @*/ String ident() {
	return delegee.ident();
    }

    /** Returns the return type of this method declaration. If this
     * method declaration is a constructor, the returned object is the
     * object denoting the void type.
     */
    public /*@ pure @*/ CType returnType() {
	return delegee.returnType();
    }

    public /*@ pure @*/ CClassType[] getExceptions() {
	return delegee.getExceptions();
    }

    public /*@ pure @*/ long modifiers() {
	return delegee.modifiers();
    }

    /** Sets the modifiers of this method declaration */
    public void setModifiers(long modifiers) {
	delegee.setModifiers(modifiers);
    }

    /**
     * Returns true if this method is a helper.
     */
    public /*@ pure @*/ boolean isHelper() {
        return Utils.hasFlag(modifiers(), ACC_HELPER);
    }

    /**
     * Returns true if this method is a abstract method.
     */
    public /*@ pure @*/ boolean isAbstract() {
	return Utils.hasFlag(modifiers(), ACC_ABSTRACT);
    }

    /**
     * Returns true if this method is a static method.
     */
    public /*@ pure @*/ boolean isStatic() {
	return Utils.hasFlag(modifiers(), ACC_STATIC);
    }

    /** Returns true if this method is spec_public. */
    public /*@ pure @*/ boolean isSpecPublic() {
        return Utils.hasFlag(modifiers(), ACC_SPEC_PUBLIC);
    }

    /** Returns true if this method is spec_protected. */
    public /*@ pure @*/ boolean isSpecProtected() {
        return Utils.hasFlag(modifiers(), ACC_SPEC_PROTECTED);
    }

    /** Returns true if this method is a public method. */
    public /*@ pure @*/ boolean isPublic() {
        return Utils.hasFlag(modifiers(), ACC_PUBLIC);
    }

    /** Returns true if this method is a private method. */
    public /*@ pure @*/ boolean isPrivate() {
        return Utils.hasFlag(modifiers(), ACC_PRIVATE);
    }


    /** Returns true if this method is a native method. */
    public /*@ pure @*/ boolean isNative() {
        return Utils.hasFlag(modifiers(), ACC_NATIVE);
    }

    /** Returns true if this method is a model method. */
    public /*@ pure @*/ boolean isModel() {
        return Utils.hasFlag(modifiers(), ACC_MODEL);
    }

    /** Returns true if this method is marked for extraction of a model program. */
    public /*@ pure @*/ boolean shouldExtract() {
        return Utils.hasFlag(modifiers(), ACC_EXTRACT);
    }

    /** Returns true if this method is a constructor. */
    public /*@ pure @*/ boolean isConstructor() {
        return false;
    }

    /** Returns true if this method is a finalizer. */
    public /*@ pure @*/ boolean isFinalizer() {
        return "finalize".equals(ident()) &&
            parameters().length == 0;
    }

    public /*@ pure */ boolean isDeclaredNonNull() {
	return delegee.isDeclaredNonNull();
    }

    /** Returns true if this method is a model method and can be
     * executed by simply commenting out annotation markers. This
     * method must be called after typechecking. */
    public /*@ pure @*/ boolean isExecutableModel() {
        return isModel() && hasBody() &&
            !((JmlSourceClass) getMethod().owner()).isEffectivelyModel();
    }

    public /*@ pure @*/ JBlock body() { 
	return delegee.body();
    }

    /** Set the name of this method; used by RAC. */
    public void setIdent(String name) {
	delegee.setIdent(name);
    }

    /** Set the body of this method. */
    public void setBody(JBlock body) {
	delegee.setBody(body);
    }

    /** Return <code>true</code> if this method declaration overrides
     * any of its superclass (or interfaces) method declarations.
     */
    public /*@ pure @*/ boolean isOverriding() {
	return delegee.isOverriding();
    }    

    /** Return the set of methods that are directly overriden (specialized)
     * by this method declaration.
     */
    public /*@ pure nullable @*/ CMethodSet overriddenMethods() {
	return delegee.overriddenMethods();
    }   

    /**
     * Indicates whether this method uses multiple dispatch
     *
     * @return	true iff a parameter of this method has a dynamic dispatch
     *		annotation or, for an external method, this methods receiver
     *		is of a different type than the generic function's top method
     */
    public boolean usesMultipleDispatch() {
	return delegee.usesMultipleDispatch();
    }

    /**
     * Compares this method to a given method and returns 0 if the
     * methods belong to the same generic function, otherwise returns
     * -1 or +1 to sort the methods.  This comparator is used to
     * separate methods by generic function in the
     * MJGenericFunctionDispatcher class.
     *
     * @param	o	the object to be compared against, must be a
     *			JMethodDeclarationType
     * @return	-1, +1, or 0
     * @exception ClassCastException if <code>o</code> is not an instance of
     *					CType */
    public /*@ pure @*/ int compareTo(/*@ non_null @*/ Object o)
            throws ClassCastException {
	return delegee.compareTo(o);
    }

    /**
     * Indicates whether this member is external.  Always returns
     * false for this but is overridden for external subclasses.
     * @return	a flag indicating whether this member is external
     */
    public /*@ pure @*/ boolean isExternal() {
	return delegee.isExternal();
    }

    /**
     * @return	the member access information object for this member.
     */
    public JmlMemberAccess jmlAccess() {
	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	return self.jmlAccess();
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Checks the basic interfaces to make sure things
     * generally look OK.  This pass gathers information about
     * the type signatures of everything (imported class
     * files, classes being compiled, methods, fields, etc...)
     * needed for the later passes.  This information is stored 
     * in a context hierarchy that is bound to the AST.
     *
     * @return	a source code representation of the method, iff sub tree 
     *		is correct enough to check code
     * @exception	PositionedError	an error with reference to the 
     *					source file
     */
    public CMember checkInterface( CContextType context ) 
	throws PositionedError 
    {
	// This is where the links between the AST and the signature 
	// objects are created (in both directions).  
	JmlSourceMethod method 
	    = (JmlSourceMethod) delegee.checkInterface( context );
	method.setAST(this);
	checkNullityAdjustType(context);
	return method;
    }

    /**
     * Performs the interface checks that are common to all sorts
     * of methods. Gets the signatures of the return type,
     * parameters and exceptions, and generates the source code
     * representation, CSourceMethod.
     *
     * @param	context		the context in which this method appears
     * @param	access		the member access for this method 
     * @param	ident		the method name (passed as a parameter 
     *				instead of using the field to properly 
     *				handle constructors where the field is 
     *				the class name but ident is &lt;init&gt;
     * @return	a source code representation of the method, iff sub tree 
     *		is correct enough to check code
     * @exception	PositionedError	an error with reference to the 
     *					source file
     */
    public CSourceMethod checkInterfaceType( CContextType context,
					     MemberAccess access, 
					     String ident) 
	throws PositionedError
    {
	return delegee.checkInterfaceType( context, access, ident );
    }
    
    public void resolveExtMethods(CContextType context) {
	delegee.resolveExtMethods( context );
    }

    /**
     * Finds the top method of every declared method.  Called after
     * the checkInitializers pass.  This cannot be done before then
     * because the external generic function mappings are not complete
     * until the end of the checkInterface pass and the constant value
     * specializers are not known until after the checkInitializers
     * pass.  This must be done before the typecheck pass so that all
     * specialized argument positions for generic functions are known
     * for ambiguity checking. */
    public void resolveTopMethods() throws PositionedError {
	delegee.resolveTopMethods();
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Creates a context for this method declaration AST node.
     *
     * @param	parent		the parent context
     */
    public CMethodContextType createSelfContext(CClassContextType parent) {
	return delegee.createSelfContext( parent );
    }

    /**
     * Computes the values of specializer expressions used to dispatch on
     * compile-time constants.
     *
     * @param	context		the context in which this class 
     *				declaration appears
     * @exception PositionedError if the check fails */
    public void resolveSpecializers(CContextType context)
	throws PositionedError {
	delegee.resolveSpecializers( context );
    }
    
    /**
     * Typechecks this method declaration.  Mutates the context to
     * record the information gathered during the checks.
     *
     * @param context the context in which this method appears
     * @exception PositionedError if the checks fail and the failure
     * cannot be recovered from */
    public void typecheck( CContextType context ) throws PositionedError 
    {  	
    	final long modifiers = modifiers();
	CClassContextType cContext = (CClassContextType) context;
    	
	try {
	    enterSpecScope(modifiers); // enter spec scope if model method

	    checkMathModes(context);

	    // !FIXME! Maybe we can do more ambitious checking here such as
	    // checking for assignments to non-assignable variables by 
	    // combining typechecking results of both the spec and the method,
	    // or by passing the result of the method to the typechecking
	    // process of the specification.

	    // !FIXME! formal parameters are checked twice, one for spec and
	    // the other for the method itself.      

	    // typecheck the method itself
	    delegee.typecheck( cContext );

	    // checkNullityAdjustType(context); <-- done in
	    // checkInterface since we need superclass method return types to
	    // have been adjusted before be typecheck this method.

	    JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	    checkRefinementConsistency(context);

	    if (hasBody()) {
		if (self.isModel()) {
			
		  	if(self.isStatic()){
	    		if(self.owner().isInterface()){
//	              no support in AspectJML --- [[[hemr]]]
			    	check(context, 
			    			false,
			    			JmlMessages.NO_SUPPORT_STATIC_MODEL_METHOD_ON_INTERFACE);
	    		}
	    	}
			
		    // make sure there is only one body defined for this method 
		    JmlMemberDeclaration refinedMeth = getRefinedMember();
		    if (refinedMeth instanceof JmlMethodDeclaration) {
			check( context,
			       ((JmlMethodDeclaration)refinedMeth)
			       .findDeclWithBody() == null,
			       JmlMessages.MODEL_METHOD_WITH_MORE_THAN_ONE_BODY,
			       this.stringRepresentation() );
		    }
		} else {
		    // make sure that the body of non-model methods only 
		    // occur in a '.java' file.
		    check( context,
			   self.inJavaFile(),
			   JmlMessages.METHOD_BODY_NOT_IN_JAVA_FILE );
		}
	    }

//	    if (Main.jmlOptions.nonnull()) {
//	    	if (NonNullStatistics.hmArgs.
//	    			containsKey(Utils.getFilePath(getTokenReference().file()))
//	    			&& (context instanceof JmlContext))
//	    	{
//	    		NonNullStatistics.handleMethodDeclaration(this, delegee, 
//	    				Utils.getFilePath(getTokenReference().file()),
//	    				(JmlContext) context);
//	    		accumulateNonNullStats((JmlContext)context);
//	    	}
//	    }

	    /* rzakhejm start */
	    /* Admissibility check:
	     * if ownership admissibility checks are enabled,
	     * one must check that if a method is not declared private, then its
	     * return type and its parameters are not declared as rep.
	     * 
	     * Model methods are currently treated as normal methods, but actually
	     * still need some consideration. 
	     */
	    if (JmlAdmissibilityVisitor.isAdmissibilityOwnershipEnabled()) {
	    	if (!hasFlag(modifiers, ACC_PRIVATE)) {
	    		if (returnType().isClassType() &&
	    				(((CClassType) returnType()).getCUniverse() instanceof CUniverseRep)) {
		    		warn(context, JmlMessages.NOT_ADMISSIBLE_REP_METHOD_PRIVATE);
	    		}
	    		JFormalParameter[] jf = parameters();
	    		for (int i = 0; i < jf.length; i++) {
		    		if (jf[i].getType().isClassType() &&
		    				(((CClassType) jf[i].getType()).getCUniverse() instanceof CUniverseRep)) {
			    		warn(context, JmlMessages.NOT_ADMISSIBLE_REP_METHOD_PRIVATE);
		    		}    			
	    		}
			}
		}
	    /* rzakhejm end */
	    
	    // typecheck JML specification if exists
	    if (methodSpecification != null) {	    	
		checkMethodSpecification(cContext, self);
            }

	    if(isOverriding()) {
		checkNullityForOverriddenMethods(context, self);
	    }
	}
	finally{
	    exitSpecScope(modifiers);
	}
		
    } // end of typecheck

    /** 
     * Ensures that at most one nullity modifier is used and that it
     * is applied to a reference type.  Also set the return type of
     * this method to non-null if appropriate.
     */
    private void checkNullityAdjustType(CContextType context) throws PositionedError
    {
	// Static semantics checks for nullity modifiers; also adjust the type, if necessary.
	if( returnType().isReference() ) {

	    // returnType().isReference() ==> returnType() instanceof CClassType
	    CClassType type = (CClassType) returnType();

	    // Set nullity qualifier of the type of this, if necessary.
	    if(hasFlag(modifiers(), ACC_NON_NULL)) {
		delegee.setNonNull();
	    } else if(!hasFlag(modifiers(), ACC_NULLABLE)) {
		// No explicit nullity modifier is present
		CClass clazz = context.getClassContext().getHostClass();
		if(Main.jmlOptions == null) {
		    throw new IllegalStateException("Main.jmlOptions should not be null");
		}
		if(hasFlag(clazz.access().modifiers(), ACC_NON_NULL_BY_DEFAULT)
		   || !hasFlag(clazz.access().modifiers(), ACC_NULLABLE_BY_DEFAULT)
		   && Main.jmlOptions.defaultNonNull()) {
		    delegee.setNonNull();
		}
	    }
	} else {
	    // There should be no nullity modifiers.
	    check(context, 
		  !hasFlag(modifiers(), NULLITY_MODS),
		  JmlMessages.NULLITY_MODIFIERS_FOR_NON_REF_TYPE,
		  new Object[] { CTopLevel.getCompiler().modUtil()
				 .asString(modifiers() & NULLITY_MODS).trim(), 
				 returnType() });
	}
    }

    private void checkNullityForOverriddenMethods(CContextType context, 
						       JmlSourceMethod self)
	throws PositionedError
    {
	// System.err.println("\t" + stringRepresentation() + ": " + overriddenMethods());
	CAbstractMethodSet.Iterator iter = overriddenMethods().iterator();
	while (iter.hasNext()) {
	    CMethod overriddenMethod = (CMethod) iter.next();
	    if (overriddenMethod instanceof JmlSourceMethod) {
		checkParamNullity(context, self, (JmlSourceMethod)overriddenMethod);
		checkResultNullity(context, self, (JmlSourceMethod)overriddenMethod);
	    }
	}
    }

    /**
     * Ensure that nullity modifiers of the parameter(s) of
     * <code>self</code> exactly match with the corresponding
     * parameter(s) of <code>overriddenMeth</code>, a method that it
     * overrides.
     */
    private void checkParamNullity(CContextType context, 
				   JmlSourceMethod self, 
				   JmlSourceMethod overriddenMeth)
	throws PositionedError
    {
	JFormalParameter[] myParameters = parameters();
	JFormalParameter[] otherParameters = overriddenMeth.getASTparameters();

	for (int i = 0; i < myParameters.length; i++) {
	    if (otherParameters[i].isNonNull(context) == myParameters[i].isNonNull(context))
		continue;

	    Object[] msgArgs = {myParameters[i].ident(), ident(),
				overriddenMeth.owner().toString()};
	    check(context, 
		  false,
		  JmlMessages.PARAMETER_NULLITY_MISMATCH,
		  msgArgs );
	}
    }

    /**
     * Ensure that nullity modifiers of the (return type of) <code>self</code>
     * are consistent with <code>overriddenMeth</code>, a method that it
     * overrides.  If inconsistent, then report a problem to the user.
     */
    private void checkResultNullity(CContextType context, 
				    JmlSourceMethod self, 
				    JmlSourceMethod overriddenMeth)
	throws PositionedError
    {
	// Warn if overriddenMeth is non_null and self is nullable.

	boolean isNullable = !self.isDeclaredNonNull();
	boolean om_isNonNull = overriddenMeth.isDeclaredNonNull();

	if (om_isNonNull && isNullable) {
	    Object[] msgArgs = {ident(), // stringRepresentation(),
				overriddenMeth.owner().toString()};
	    check(context, 
		  false,
		  JmlMessages.METHOD_NON_NULL_IN_SUPER,
		  msgArgs );
	}
    }

    private void checkMathModes(CContextType context) throws PositionedError
    {
    	//by default, the arithmetic types are the same as the ones of the class
    	final long modifiers = modifiers();
	//to avoid too much function calls, here is a local copy of some of
	//the booleans used to perform checking
	boolean code_java_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_JAVA_MATH);
	boolean code_safe_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_SAFE_MATH);
	boolean code_bigint_math 
	    = Utils.hasFlag(modifiers, ACC_CODE_BIGINT_MATH);
	boolean code_default 
	    = !(code_java_math||code_safe_math||code_bigint_math);
	boolean spec_java_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_JAVA_MATH);
	boolean spec_safe_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_SAFE_MATH);
	boolean spec_bigint_math 
	    = Utils.hasFlag(modifiers, ACC_SPEC_BIGINT_MATH);
	boolean spec_default 
	    = !(spec_java_math||spec_safe_math||spec_bigint_math);

	//make sure that there are no conflictual arithmetic mode flags
	if(!code_default)
	    {
		check(context,
		      !((code_java_math && code_safe_math)
			||(code_safe_math && code_bigint_math)
			||(code_java_math && code_bigint_math)
			),
		      JmlMessages.ARITHMETIC_MODE_CONFLICT
		      );
	    }
	if(!spec_default)
	    {
		check(context,
		      !((spec_java_math && spec_safe_math)
			||(spec_safe_math && spec_bigint_math)
			||(spec_java_math && spec_bigint_math)
			),
		      JmlMessages.ARITHMETIC_MODE_CONFLICT
		      );
	    }
    }

    private void checkMethodSpecification(CClassContextType cContext, 
					  JmlSourceMethod self) 
	throws PositionedError 
    {
		// Stores the definite assignment status of the fields
		// after executing the constructor.
		CVariableInfoTable actualFieldInfo = cContext.fieldInfoTable();
		
		try {
                    enterSpecScope();                    
		    
                    // create typechecking context
		    resetFinalFieldStatusIfConstructor(cContext);
                    CMethodContextType mctx = 
                        createSelfContext(cContext);
                    CFlowControlContextType fctx = 
                       mctx.createFlowControlContext(self.parameters().length,
						     getTokenReference());

                    // add local vars, first this and then formal parameters
                    if (!self.isStatic()) {
                        fctx.addThisVariable();
                    }
                    for (int i = 0; i < delegee.parameters().length; i++) {
                        delegee.parameters()[i].typecheck( fctx );
                    }

                    // typecheck the model program spec cases
                    methodSpecification.typecheckModelPrograms( fctx );

		    // -----------------------------------------------------

		    // Now reset to the actual scope of the constructor for
		    // checking the other specification cases
		    cContext.setFieldInfoTable(actualFieldInfo);
                    mctx = createSelfContext(cContext);
                    fctx = mctx.createFlowControlContext(
			self.parameters().length, getTokenReference());

                    // add local vars, first this and then formal parameters
                    if (!self.isStatic()) {
                        fctx.addThisVariable();
                    }
                    for (int i = 0; i < delegee.parameters().length; i++) {
                        delegee.parameters()[i].typecheck( fctx );
                    }
		    methodSpecification.typecheck( fctx );

		    jmlchecks(cContext, self);
                }
                finally {
                    exitSpecScope();
                }
    } // end of checkMethodSpecification


    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Generates a sequence of bytecodes
     * @param	code		the code list
     */
    public void genCode(CodeSequence code) {
	delegee.genCode( code );
    }

    /**
     * Resets the final field definite assignment info if this is a
     * constructor.
     */
    protected void resetFinalFieldStatusIfConstructor(CClassContextType context){
	// do nothing, overridden in subclass
    }

    public void jmlchecks(CContextType context, JmlSourceMethod self) 
	throws PositionedError 
    {
	// The specification must begin with 'also' iff it overrides a method 
	// in a parent class.

	overriddenMethodSet = overriddenMethods();
	boolean overrides = isOverriding();
	boolean refines = (refinedDecl != null);
	/*@ nullable @*/ JmlSourceMethod overriddenMeth = null;

	if (overriddenMethodSet != null) {
	    CAbstractMethodSet.Iterator iter = overriddenMethodSet.iterator();
	    while (iter.hasNext()) {
		CMethod currMeth = (CMethod) iter.next();
		if (currMeth instanceof JmlSourceMethod) {
		    JmlMethodSpecification specs 
			= ((JmlSourceMethod)currMeth).getSpecification();
		    if (specs != null) {
			overriddenMeth = (JmlSourceMethod) currMeth;
		    }
		}
	    }

	    // Only one overridden method instance has to be checked 
	    // (if it has a specification) 
	    // because the parameter names have to be consistent 
	    // in a refinement sequence (this is enforced by the 
	    // code above in method 'checkRefineConsistency'). 
	    if (overriddenMeth != null) {
		JFormalParameter[] myParameters = delegee.parameters();
		JFormalParameter[] otherParameters
		    = overriddenMeth.getASTparameters();
		for (int k=0; k<myParameters.length; k++) {
		    String parm = myParameters[k].ident();
		    String refinedParm = otherParameters[k].ident();
		    if (! parm.equals(refinedParm) ) {
			CClass thisOwner = self.owner();
			java.io.File thisFile = thisOwner.sourceFile();
			java.io.File overriddenFile 
			    = overriddenMeth.owner().sourceFile();
			Object[] msgArgs = {stringRepresentation(), 
					    parm, thisFile.getName(), 
					    refinedParm, 
					    overriddenFile.getName()};
			warn(context, 
			     JmlMessages.NON_MATCHING_PARAMETER_NAME, 
			     msgArgs );
		    }
		}
	    }
	}

	// Note: a spec starting with also is parsed as a 
	// JmlExtendingSpecification; one without an initial
	// also is parsed as a JmlSpecification; 
	// JmlExtendingSpecification is a subclass of JmlSpecification
	boolean hasAlso 
	    = (methodSpecification instanceof JmlExtendingSpecification);

	if (hasAlso) {
	    if (!overrides && !refines) {
		if (this instanceof JmlConstructorDeclaration) {
		    warn(context, JmlMessages.EXTRANEOUS_ALSO, 
			 stringRepresentation() );
		} else {
		    warn(context, JmlMessages.EXTRANEOUS_ALSO, 
			 stringRepresentation() );
		}
	    }
	} else {
	    if (overrides) {
		CMethod othMeth = (CMethod) overriddenMethodSet.getFirst();
		String othMethStringRep = othMeth.toString();
		
		// check if the method is a PC method --- [[[hemr]]]
		boolean canCheck = true;
		List<JavaMethod> javaMeths = AspectUtil.getInstance().getAllDeclaredJavaMethodsInFile(othMeth.getJavaName().replace("."+othMeth.ident(), ""));
		String jmlMeth = othMeth.getIdent()+AspectUtil.generateMethodParameters(othMeth.parameters());
		if(javaMeths != null){
			for (Iterator<JavaMethod> iterator = javaMeths.iterator(); iterator.hasNext();) {
				JavaMethod currentJavaMeth = iterator.next();
				String currentMethSig = currentJavaMeth.getName()+AspectUtil.generateMethodParameters(currentJavaMeth.getParameters(), false);
				if(jmlMeth.equals(currentMethSig)){
					if(QDoxUtil.iPCXCS(currentJavaMeth)){
						canCheck = false;
					}
				}
			}
		}
		
		if(canCheck){
			warn(context, JmlMessages.MISSING_ALSO, stringRepresentation(), 
				     othMethStringRep );
		}
	    } else if (refines) {
	    	JmlSourceMethod refinedSrcMeth 
	    	= (JmlSourceMethod) refinedDecl.getMethod();
	    	CClass refinedOwner = refinedSrcMeth.owner();
	    	java.io.File refinedFile = refinedOwner.sourceFile();
	    	String refinedFileName = refinedFile.getName();
	    	warn(context, JmlMessages.MISSING_REFINING_ALSO, 
	    			stringRepresentation(), refinedFileName );
	    }
	}
	if (methodSpecification != null && this.isAbstract()) {
	    // abstract methods cannot have a code specification
	    if (methodSpecification.hasSpecCases() ) {
		JmlSpecCase[] specCases = methodSpecification.specCases();
		for (int i=0; i<specCases.length; i++) {
		    if ( specCases[i].isCodeSpec() ) {
			warn(context, JmlMessages.ILLEGAL_CODE_MODIFIER, 
			     stringRepresentation());
		    }
		}
	    }
	}

    }

    /**
     * Returns the maximal set of fields that can be assigned to by 
     * this method (takes the union of the assignable clauses from 
     * all specification cases).
     */
    public JmlAssignableFieldSet getAssignableFieldSet() 
    {
	if ( assignableFieldSet != null ) {
	    return assignableFieldSet;
	}

	// If pure, then return the empty JmlAssignableFieldSet
	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	if ( self.isPure() && !self.isConstructor() ) {
	    assignableFieldSet = new JmlAssignableFieldSet();
	    return assignableFieldSet;
	}

	boolean hasNoSpecification = true;
	if (combinedMethodSpecification != null) {
	    assignableFieldSet 
		= combinedMethodSpecification.getAssignableFieldSet(self);
	    // don't want to modify the original so need to clone the set
	    assignableFieldSet 
		= (JmlAssignableFieldSet) assignableFieldSet.clone();

	    if ( assignableFieldSet == null ) {
		// this occurs when the specification is a code_contract 
		// which has no assignable clause
		assignableFieldSet = new JmlAssignableFieldSet();
	    } else {
		hasNoSpecification = false;
	    }
	} else {
	    assignableFieldSet = new JmlAssignableFieldSet();
	}

	overriddenMethodSet = overriddenMethods();
	if (overriddenMethodSet != null) {
	    CAbstractMethodSet.Iterator iter = overriddenMethodSet.iterator();
	    while (iter.hasNext()) {
		CMethod currMeth = (CMethod) iter.next();
		if (currMeth instanceof JmlSourceMethod) {
		    JmlSourceMethod overriddenMeth 
			= (JmlSourceMethod) currMeth;
		    JmlMethodDeclaration methodDecl 
			= (JmlMethodDeclaration) overriddenMeth.getAST();
		    JmlAssignableFieldSet fields 
			= methodDecl.getAssignableFieldSet();
		    if (fields != null) {
			if (!fields.isNotSpecified()) {
			    hasNoSpecification = false;
			    // ignore inherited spec if not specified
			    if (assignableFieldSet.isNotSpecified()) {
				// inherit the specification
				// from the overridden method and 
				// ignore this (non)specification
				assignableFieldSet 
				    = (JmlAssignableFieldSet) fields.clone();
			    } else {
				assignableFieldSet.addAll(fields);
			    }
			}
		    }
		}
	    }
	}

	if ( hasNoSpecification ) {
	    assignableFieldSet.setNotSpecified();
	}
	return assignableFieldSet;
    }

    /**
     * Returns the minimal set of fields that can be assigned to by 
     * this method (takes the intersection of the assignable clauses from 
     * the specification cases). This set is used in the checking of 
     * assignable fields when there are calls in the method body.  
     */
    public JmlAssignableFieldSet getMinAssignableFieldSet(
					  JmlDataGroupMemberMap dataGroupMap ) 
    {
	if ( minAssignableFieldSet != null ) {
	    return minAssignableFieldSet;
	}

	// If pure, then return the empty JmlAssignableFieldSet
	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	if ( self.isPure() && !self.isConstructor() ) {
	    minAssignableFieldSet = getAssignableFieldSet();
	    return minAssignableFieldSet;
	}

	boolean hasNoSpecification = true;
	if (combinedMethodSpecification != null) {
	    minAssignableFieldSet 
		= combinedMethodSpecification
		.getMinAssignableFieldSet(self, dataGroupMap);
	    // intersect doesn't modify the original so no need to clone
	    // in above statement

	    if ( minAssignableFieldSet == null ) {
		// this occurs when the specification is a code_contract 
		// which has no assignable clause
		minAssignableFieldSet = new JmlAssignableFieldSet();
	    } else {
		hasNoSpecification = false;
	    }
	} else {
	    minAssignableFieldSet = new JmlAssignableFieldSet();
	}

	overriddenMethodSet = overriddenMethods();
	if (overriddenMethodSet != null) {
	    CAbstractMethodSet.Iterator iter = overriddenMethodSet.iterator();
	    while (iter.hasNext()) {
		CMethod currMeth = (CMethod) iter.next();
		if (currMeth instanceof JmlSourceMethod) {
		    JmlSourceMethod overriddenMeth 
			= (JmlSourceMethod) currMeth;
		    JmlMethodDeclaration methodDecl 
			= (JmlMethodDeclaration) overriddenMeth.getAST();
		    JmlAssignableFieldSet fields 
			= methodDecl.getMinAssignableFieldSet(dataGroupMap);
		    if (fields != null) {
			if (!fields.isNotSpecified()) {
			    hasNoSpecification = false;
			    // ignore inherited spec if not specified
			    minAssignableFieldSet 
				= minAssignableFieldSet
				.intersect(fields, dataGroupMap);
			}
		    }
		}
	    }
	}

	if ( hasNoSpecification ) {
	    minAssignableFieldSet.setNotSpecified();
	}
	return minAssignableFieldSet;
    }

    public void checkAssignableFields( JmlDataGroupMemberMap dataGroupMap )
    {
	JBlock body = body();
	if (body == null) {
	    return;
	}
	// System.out.println("checking assignable fields for :"+this.ident());
    
	getAssignableFieldSet();

	JmlAccumSubclassingInfo accum = new JmlAccumSubclassingInfo();
	body.accept(accum);
	assignedFields = accum.getAssignedFields();
	accessedFields = accum.getAccessedFields();
	calledMethods = accum.getCalledMethods();

	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();

	// Check assignment statements
	for (int i=0; i<assignedFields.length; i++) {
	    if (assignedFields[i] instanceof JClassFieldExpression) {
		JClassFieldExpression fieldExpr 
		    = (JClassFieldExpression)assignedFields[i];
		if ( assignableFieldSet != null
		     && !assignableFieldSet.contains(fieldExpr, 
						     dataGroupMap)) {
		    Object msgArgs[] = new Object[4];
		    msgArgs[0] = fieldExpr.ident();
		    msgArgs[1] = this.stringRepresentation();
		    msgArgs[2] = assignableFieldSet.toString();
		    CTopLevel.getCompiler().reportTrouble(
		            new PositionedError( 
			            fieldExpr.getTokenReference(),
				    JmlMessages.NOT_ASSIGNABLE_FIELD,
				    msgArgs )
			    );
		// System.err.println("data group map "+"\n"+dataGroupMap);
		}

		// The following check should be removed as soon as 
		// dynamic dependency checking is added.  

		JExpression prefix = fieldExpr.prefix();
		JLocalVariable var = null;
		if (prefix instanceof JLocalVariableExpression) {
		    var = ((JLocalVariableExpression)prefix).variable();
		}
		if ( (var instanceof JFormalParameter)
		     || !(prefix instanceof JLocalVariableExpression) ) {
		    if ( assignableFieldSet != null
			 && assignableFieldSet.isEmpty() ) {
			Object msgArgs[] = new Object[4];
			msgArgs[0] = fieldExpr.ident();
			msgArgs[1] = this.stringRepresentation();
			msgArgs[2] = assignableFieldSet.toString();
			CTopLevel.getCompiler().reportTrouble(
		                new PositionedError( 
			            fieldExpr.getTokenReference(),
				    JmlMessages.NOT_ASSIGNABLE_FIELD,
				    msgArgs )
			    );
		    }
		}
	    }
	} // end of for loop

	// Check method calls
	for (int i=0; i<calledMethods.length; i++) {
	    JMethodCallExpression methodCall
		= (JMethodCallExpression) calledMethods[i];
	    CMethod calledMeth = methodCall.method();
	    if (calledMeth instanceof JmlSourceMethod) {
		JmlSourceMethod calledMethSrc 
		    = (JmlSourceMethod) calledMeth;
		JmlMethodDeclaration calledMethDecl 
		    = (JmlMethodDeclaration) calledMethSrc.getAST();
		JmlAssignableFieldSet calledAssignable 
		    = calledMethDecl.getMinAssignableFieldSet(dataGroupMap);
		JExpression prefix = methodCall.prefix();
		if (prefix instanceof JThisExpression) {
		    if ( !calledAssignable
			 .isSubsetOf(assignableFieldSet, dataGroupMap) ) {
			if ( Main.jmlOptions.Assignable() 
			     || !calledAssignable.isNotSpecified() ) {
			    Object msgArgs[] = new Object[4];
			    msgArgs[0] = stringRepresentation();
			    msgArgs[1] = assignableFieldSet.toString();
			    msgArgs[2] = calledMethDecl.stringRepresentation();
			    msgArgs[3] = calledAssignable.toString();
			    CTopLevel.getCompiler().reportTrouble(
		                new PositionedError( 
			            methodCall.getTokenReference(),
				    JmlMessages.NOT_CALLABLE_METHOD,
				    msgArgs )
				);
			    // no need to get another error from the next check
			    continue;
			// System.err.println("data group map "+"\n"+dataGroupMap);
			}
		    }
		} 

		// The following check should be removed as soon as 
		// dynamic dependency checking is added.  

		// The next check makes sure that pure methods 
		// do not modify the state of objects referenced 
		// by fields or parameters, i.e., calls to methods 
		// with side-effects on fields or parameters are 
		// not allowed. 
		// (but side-effects on local variables are ignored.)

		JLocalVariable var = null;
		if (prefix instanceof JLocalVariableExpression) {
		    var = ((JLocalVariableExpression)prefix).variable();
		}
		if ( (var instanceof JFormalParameter)
		     || !(prefix instanceof JLocalVariableExpression) ) {
		    if ( assignableFieldSet.isEmpty()
			 && !calledAssignable.isEmpty() ) {
			if ( Main.jmlOptions.Assignable() 
			     || !calledAssignable.isNotSpecified() ) {
			    CTopLevel.getCompiler().reportTrouble(
		                new PositionedError( 
			            methodCall.getTokenReference(),
				    JmlMessages.PURE_AND_CALLS_NON_PURE,
				    this.stringRepresentation(),
				    calledMethDecl.stringRepresentation()
				    )
				);
			}
		    }
		}

	    }
	} // end of for loop
    }

    /**
     * Checks that this method appropriately overrides the given
     * superclass methods.  The checks are those given in JLS2,
     * section 8.4.6.3 and CLCM 00 4.1.3.1 (extended per Clifton's
     * thesis).
     *
     * @param	context		the context in which this appears
     * @param superMethods      the super type methods that this
     *                          <em>may</em> override
     * @exception PositionedError if a check fails */
    public void checkOverriding( CContextType context, CMethodSet superMethods ) 
	throws PositionedError 
    {
	delegee.checkOverriding( context, superMethods );
    }

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlMethodDeclaration( this );
	else
	    super.accept( p );
    }

    public void acceptDelegee( MjcVisitor p) {
	p.visitMethodDeclaration( delegee);
    }

    //---------------------------------------------------------------------
    // REFINEMENT
    //---------------------------------------------------------------------

    /**
     * @return	the name representation of this member.
     */
    public String stringRepresentation() {
	if (thisStringRep != null) {
	    return thisStringRep;
	}
	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	thisStringRep = self.toString();
	int pos = thisStringRep.indexOf(".<init>");
	if (pos != -1) {
	    // 7 for length of ".<init>"
	    thisStringRep = thisStringRep.substring(0,pos)
		+ thisStringRep.substring(pos+7);
	}
	return thisStringRep;
    }

    /**
     * Calculates and returns the method refined by this
     * method.  Caches the result for later calls to 
     * {@link #getRefinedMember()}.
     * Also sets the refining method of the method returned 
     * so they are linked to each other.
     */
    protected void setRefinementLinks() {
	JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	if (refinedDecl == null) {
	    // has NOT already been set 

	    // compute and then set the refined method 
	    JmlSourceClass ownerClass = (JmlSourceClass) self.owner();
	    JmlSourceMethod refinedSrc = ownerClass.lookupRefinedMethod(self);
	    if (refinedSrc != null) {
		JmlMemberDeclaration refinedMethod = refinedSrc.getAST();
		refinedDecl = refinedMethod;
		refinedMethod.setRefiningMember(this);
	    }
	}
    }

    protected void setRefiningMethod(JmlMethodDeclaration refiningMethod) {
	refiningDecl = refiningMethod;
    }

    public void checkRefinementConsistency( CContextType context )
	throws PositionedError 
    {
	if (refinedDecl != null) {
	    JmlSourceMethod self = (JmlSourceMethod) delegee.getMethod();
	    // Check the modifiers common to methods and fields
	    JmlMemberAccess selfAccess = this.jmlAccess();
	    checkRefinedModifiers(context, this);

	    JmlSourceMethod refinedSrcMeth 
		= (JmlSourceMethod) refinedDecl.getMethod();
	    CClass refinedOwner = refinedSrcMeth.owner();
	    java.io.File refinedFile = refinedOwner.sourceFile();
	    String refinedFileName = refinedFile.getName();

	    // Check consistency of formal parameters.
	    JFormalParameter[] myParameters = delegee.parameters();

	    // check that corresponding parameters:
	    // (1) have the same names
	    // (2) have the same nullity modifier.
	    JFormalParameter[] otherParameters
		= refinedSrcMeth.getASTparameters();
	    for (int k=0; k<myParameters.length; k++) {
		String parm = myParameters[k].ident();
		String refinedParm = otherParameters[k].ident();

		// check names
		if (! refinedParm.equals("") && ! refinedParm.equals(parm) ) {
		    CClass thisOwner = self.owner();
		    java.io.File thisFile = thisOwner.sourceFile();
		    Object[] msgArgs = {stringRepresentation(), 
					parm, thisFile.getName(), 
					refinedParm, refinedFileName};
		    warn(context, 
			 JmlMessages.INVALID_REFINING_PARAMETER_NAME, 
			 msgArgs );
		}
		// check that nullity modifiers match
		if(myParameters[k].isNonNull(context) 
		   != otherParameters[k].isNonNull(context))
		{
		    Object[] msgArgs = {stringRepresentation(), // method name
					parm, 
					myParameters[k].isNonNull(context) ? "non_null " : "nullable ",
					otherParameters[k].isNonNull(context) ? "non_null " : "nullable ",
					refinedFileName};
		    warn(context, 
			 JmlMessages.INVALID_REFINING_PARAMETER_NULLITY, 
			 msgArgs );
		}

	    }

	    JmlMemberAccess refinedAccess = refinedSrcMeth.jmlAccess();
	    Object msgArgs[] = new Object[4];

	    // check to make sure the return types are the same
	    msgArgs[0] = stringRepresentation();
	    msgArgs[1] = refinedFileName;
	    msgArgs[2] = refinedSrcMeth.returnType().toString();
	    check( context,
		   self.returnType().equals(refinedSrcMeth.returnType()),
		   JmlMessages.REFINING_METHOD_RETURN_DIFFERENT, 
		   msgArgs  );

	    // check the throws clause
	    CClassType[] refinedExc = refinedSrcMeth.throwables();
	    CClassType[] exceptions = self.throwables();
	
	    msgArgs[0] = stringRepresentation();
	    msgArgs[1] = refinedFileName;
	  loop:
	    for (int j = 0; j < exceptions.length; j++) {
		if (exceptions[j].isCheckedException()) {
		    for (int k = 0; k < refinedExc.length; k++) {
			if (exceptions[j].isAlwaysAssignableTo(refinedExc[k])) {
			    continue loop;
			}
		    }
		    msgArgs[2] = exceptions[j];
		    check( context, 
			   false, 
			   JmlMessages.REFINING_METHOD_THROWS_DIFFERENT, 
			   msgArgs );
		}
	    }		

	    // Check the Java modifiers
	    // selfAccess.isAbstract() <==> refinedAccess.isAbstract()
	    if ( selfAccess.isAbstract() ) {
		msgArgs[0] = "Abstract";
		msgArgs[2] = "non-abstract";
		check( context,
		       refinedAccess.isAbstract(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-abstract";
		msgArgs[2] = "abstract";
		check( context,
		       !refinedAccess.isAbstract(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // refinedSrcMeth.isPure() ==> self.isPure()
	    msgArgs[1] = stringRepresentation();
	    msgArgs[3] = refinedFileName;
	    if ( refinedSrcMeth.isPure() ) {
		msgArgs[0] = "Non-pure";
		msgArgs[2] = "pure";
		check( context, 
		       self.isPure(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // selfAccess.isHelper() <==> refinedAccess.isHelper()
	    if ( selfAccess.isHelper() ) {
		msgArgs[0] = "Helper";
		msgArgs[2] = "non-helper";
		check( context,
		       refinedAccess.isHelper(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-helper";
		msgArgs[2] = "helper";
		check( context,
		       !refinedAccess.isHelper(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    msgArgs[1] = thisStringRep;
	    msgArgs[3] = refinedFileName;
	    // selfAccess.isNullable() <==> refinedAccess.isNullable()
	    if ( self.isDeclaredNonNull() ) {
		msgArgs[0] = "Non-null";
		msgArgs[2] = "nullable";
		check( context,
		       !(refinedSrcMeth.returnType().isReference()
			 && !refinedSrcMeth.isDeclaredNonNull()),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Nullable";
		msgArgs[2] = "non-null";
		check( context,
		       !(returnType().isReference()
			 && refinedSrcMeth.returnType().isReference()
			 && refinedSrcMeth.isDeclaredNonNull()),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	} 
    }

    //---------------------------------------------------------------------
    // COMBINE SPECIFICATIONS
    //---------------------------------------------------------------------

    public void setSpecstoCombinedSpecs() {
	methodSpecification = combinedMethodSpecification;
    }

    /**
     *  Returns the method specifications of this member declaration 
     *  combined with the specifications of those it refines.
     *  Returns null if it does not have any combined method specifications.
     */
    public JmlMethodSpecification getCombinedSpecification() {
	return combinedMethodSpecification;
    }

    public void combineSpecifications() 
    {
	if (combinedMethodSpecification != null) {
	    return;
	}
	if (! this.isRefiningMember()) {
	    combinedMethodSpecification = methodSpecification;
	} else {
	    // combine specs of the refined method declaration

	    JmlMemberDeclaration refinedMethod = getRefinedMember();
	    refinedMethod.combineSpecifications();
	    JmlSpecification refSpec 
		= (JmlSpecification) 
		refinedMethod.getCombinedSpecification();

	    if (refSpec == null) {
		combinedMethodSpecification = methodSpecification;
	    } else if (! this.hasSpecification()) {
		combinedMethodSpecification = refSpec;
	    } else {
		// combine specs of this decl with the refined specs
		JmlSpecification selfSpec
		    = (JmlSpecification) methodSpecification;

		// combine spec cases
		JmlSpecCase[] refSpecCases = refSpec.specCases();
		JmlSpecCase[] selfSpecCases = selfSpec.specCases();
		JmlSpecCase[] combinedSpecCases
		    = (JmlSpecCase[]) Utils.combineArrays(refSpecCases, 
							  selfSpecCases);
		// combine redundant specs 
		JmlRedundantSpec combinedRedundantSpec
		    = (refSpec.redundantSpec() == null) ?
		    selfSpec.redundantSpec()
		    : refSpec.redundantSpec().combine(selfSpec.redundantSpec());

		// Note that the subclassing contract is NOT inherited
		// or combined in the refined spec
		combinedMethodSpecification
		    = refSpec.newInstance( combinedSpecCases,
					   combinedRedundantSpec);
	    }
	}
	// check that "\same" predicate in the requires clause 
	// has other specification cases that specify the precondition
	if ( !(methodSpecification instanceof JmlExtendingSpecification) ) {
	    if ( combinedMethodSpecification != null 
		 && combinedMethodSpecification.hasSpecCases() ) {
		JmlSpecCase[] allCases 
		    = combinedMethodSpecification.specCases();
		boolean hasPreCondition = false;
		boolean hasSamePreCond = false;
		for (int i=0; i<allCases.length; i++ ) {
		    // need to make sure that a single spec case does not 
		    // have a "requires \same;" clause
		    JmlGeneralSpecCase specCase = null;
		    if ( allCases[0] instanceof JmlGeneralSpecCase ) {
			specCase = (JmlGeneralSpecCase) allCases[0];
		    } else if ( allCases[0] instanceof JmlHeavyweightSpec ) {
			specCase 
			    = ((JmlHeavyweightSpec)allCases[0]).specCase();
		    }
		    if ( specCase != null && specCase.hasSpecHeader() ) {
			JmlRequiresClause req[] = specCase.specHeader();
			if ( req[0].predOrNot() != null ) {
			    if ( req[0].predOrNot().isSameKeyword() ) {
				hasSamePreCond = true;
			    } else {
				hasPreCondition = true;
			    }
			} else {
			    hasPreCondition = true;
			}
		    }
		} // end of for loop
		if ( hasSamePreCond && !hasPreCondition ) {
		    CTopLevel.getCompiler().reportTrouble(
				new PositionedError( 
				     getTokenReference(),
				     JmlMessages.ILLEGAL_SAME_PREDICATE )
				);
		}
	    }
	}

    }

    /** Sets the modifiers2 of this method declaration */
    public void setModifiers2(int modifiers2) {
	this.modifiers2 = modifiers2;
    }

    public /*@ pure @*/ int modifiers2() {
	return modifiers2;
    }

    /** 
     * Returns true if this method is a RAC method.
     * Such kind of method needs to be printed in RAC instead of
     * in mjc
     */
    public /*@ pure @*/ boolean isRacMethod() {
        return Utils.hasFlag(modifiers2(), ACC2_RAC_METHOD);
    }


    private void accumulateNonNullStats(JmlContext context) 
	throws PositionedError
    {
	if (!NonNullStatistics.hmArgs.containsKey(Utils.getFilePath(getTokenReference().file())))
	    throw new IllegalStateException();
		
	String str = Utils.getFilePath(getTokenReference().file())
	    + "|" + context.getHostClass().ident() +"|" + ident(); 
	boolean bExplicit = false;
	Vector jsc = new Vector();
	boolean[] bParam = new boolean[parameters().length]; // set to false by default init

	//method explicit
	if (overriddenMethods() != null && overriddenMethods().size() != 0 ) {
	    bExplicit = NonNullStatistics.getSuperMethod((JmlSourceMethod)delegee.getMethod());
	    //param explicit
	    for (int p=0; p<parameters().length; p++) {
		bParam[p] = NonNullStatistics.getSuperParam((JmlSourceMethod)delegee.getMethod(), p);
	    }
	    //System.out.println(" over riden methos , size is "+overriddenMethods().size());
	    jsc = NonNullStatistics.getSuperSpec(this, str);
	}

	//append methodspecification to spec case array
	if (methodSpecification != null && methodSpecification.specCases() != null)
	{
	    JmlSpecCase[] specCases = methodSpecification.specCases();

	    for (int p=0; p < specCases.length; p++) {
		JmlSpecCase sc = specCases[p];
		if(!sc.isCodeSpec()) {
		    jsc.add(sc);
		}
	    }
	    //System.out.println("method specification of method "+ident()+" is not null");
	}
		
	if (jsc.size() !=0 ){
	    //JmlSpecCase[] jscArray = new JmlSpecCase[jsc.size()];
	    Object[] jscArray = new Object[jsc.size()];
	    jsc.toArray(jscArray);
	    NonNullStatistics.setCurrClass(context.getHostClass().ident());
	    NonNullStatistics.setCurrMethod(ident());
	    NonNullStatistics.checkSpecification(this, 
						 jscArray,
						 context, 
						 Utils.getFilePath(delegee.getTokenReference().file()));
	}

	String strNonNull =Utils.getFilePath(getTokenReference().file())
	    + "|" + context.getHostClass().ident() + "|" + ident();

	//System.out.println("\taccStats: " + ident() + " " + context.getClassContext().getHostClass().toString()
	//		   + " bExplicit = " + bExplicit);


	if (hasFlag(modifiers(),ACC_PURE)){ 
	    //System.out.println("remove all implicit value in "+strNonNull);
	    if (NonNullStatistics.hmNnStat.containsKey(strNonNull)){
		String value = (String) NonNullStatistics.hmNnStat.get(strNonNull);
		if (value.compareTo("Nm")==0) {
		    NonNullStatistics.hmNnStat.remove(strNonNull);
		}
	    }
	}
	    
	JFormalParameter[] jf = parameters();
	
	boolean paramSpec = false;
	for (int p=0;p<jf.length;p++) {
	    if (jf[p] instanceof JmlFormalParameter)
		if (((JmlFormalParameter)jf[p]).isNonNull(context)) { // was - Chalin - FIXME
		    paramSpec = true;
		    break;
		}
	}
		
	boolean ifSuperSpec = false;
	if (overriddenMethods()!=null && overriddenMethods().size()!=0){
	    CMethodSet cms=overriddenMethods();
	    for (int a=0; a<cms.size();a++){
		CMethod cm = cms.getMethod(a);				
		if  (cm instanceof JmlSourceMethod){
		    JmlSourceMethod jm =(JmlSourceMethod) cm;
		    if (jm.getSpecification() !=null) {
			ifSuperSpec = true;
		    }
		}
	    }
	}

	// if method has spec, use method spec
	if ( (methodSpecification != null) 
	     || hasFlag(modifiers(),ACC_NON_NULL)
	     // || hasFlag(modifiers(),ACC_NULLABLE)
	     || paramSpec) 
	{ //explicit or implicit non_null
	    /*
	    if (isNonNull()) {
		if (hasFlag(modifiers(),ACC_MODEL)) { //Model
		    NonNullStatistics.hmNonnullPut(strNonNull,"Mm");
		} else {
		    NonNullStatistics.hmNonnullPut(strNonNull,"Rm");
		}
	    }
	    */
	    if (methodSpecification==null 
		|| (NonNullStatistics.ifFalse 
		    && methodSpecification.specCases().length==1 
		    && !ifSuperSpec )){ //remove all implicit non_null
		NonNullStatistics.hmNnStat.remove(strNonNull); //remove method implicit
		//System.out.println("remove method implicit");
		str="";
		for (int k=0; k<jf.length;k++){
		    if (jf[k] instanceof JmlFormalParameter){
			str = strNonNull +"|"
			    +((JmlFormalParameter)jf[k]).ident();
			if ( NonNullStatistics.hmNnStat.containsKey(str)) {
			    NonNullStatistics.hmNnStat.remove(str);
			}
		    }
		}		    
	    }//if
	} //if   

	/*
	// if super has explicit non_null or implicit non_null, we keep explicit non_null, or remove it  
	if (isNonNull()
	    // hasFlag(modifiers(),ACC_NON_NULL)
	    && methodSpecification == null){
	    if (!bExplicit
		&& !NonNullStatistics.hmNnStat.containsKey(strNonNull))
	    { 
		if (hasFlag(modifiers(),ACC_MODEL)
		    && delegee.returnType().isReference()){
		    //Model
		    NonNullStatistics.hmNonnullPut(strNonNull,"mm");
		}else if (delegee.returnType().isReference()){
		    //reference var
		    NonNullStatistics.hmNonnullPut(strNonNull,"rm");
		}
	    }
	}
	*/

	/*
	// param, if super has explicit or implicit, it can be explicit 
	for (int h=0; h<jf.length; h++) {
	    str="";
	    if ((jf[h] instanceof JmlFormalParameter)
		&& jf[h].getType().isReference()
		&& ((JmlFormalParameter)jf[h]).isNonNull() // was - Chalin - FIXME
		){
		str = strNonNull +"|"+((JmlFormalParameter)jf[h]).ident();
		//check superclasses' params to set current param explicit or not
		if (!(bParam[h]
		      || NonNullStatistics.hmNnStat.containsKey(str)
		      ||(context.getHostClass().ident()).equals(ident()) ))
		{
		    // if super is not explicit 
		    // System.out.println("param is not with explicit non_null in super class "+str);
		    NonNullStatistics.hmNonnullPut(str,
						   hasFlag(modifiers(),ACC_MODEL) ? "mp" : "rp");
		}
	    }
	}
	*/

    }			    

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private /*@ non_null @*/ JMethodDeclaration delegee;
    private /*@ nullable @*/ JmlMethodSpecification methodSpecification;
    private /*@ nullable @*/ CMethodSet overriddenMethodSet = null; // FIXME: I don't think we should have this field - instead use overriddenMethods()
    private /*@ nullable @*/ JmlMethodSpecification combinedMethodSpecification = null;
    private /*@ nullable @*/ JmlAssignableFieldSet assignableFieldSet = null;
    private /*@ nullable @*/ JmlAssignableFieldSet minAssignableFieldSet = null;
    private /*@ nullable @*/ JExpression[] assignedFields = null;
    private /*@ nullable @*/ JExpression[] accessedFields = null;
    private /*@ nullable @*/ JExpression[] calledMethods = null;
    private /*@ nullable @*/ String thisStringRep = null;
    private int modifiers2 = 0; // FIXME: IMHO, this is obsolete.

}// JmlMethodDeclaration
