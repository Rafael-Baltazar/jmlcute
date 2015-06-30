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
 * $Id: JmlFieldDeclaration.java,v 1.61 2008/01/08 19:57:03 chalin Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CClass;
import org.multijava.mjc.CClassContextType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.CContextType;
import org.multijava.mjc.CFlowControlContext;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CSourceField;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CUniverseRep;
import org.multijava.mjc.CodeSequence;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFieldDeclaration;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JLiteral;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.Utils;
import org.multijava.util.classfile.ClassFileReadException;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.ClassPath;
import org.multijava.util.classfile.FieldInfo;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * JmlFieldDeclaration.java
 *
 * @author Curtis Clifton
 * @version $Revision: 1.61 $
 */

public class JmlFieldDeclaration extends JmlMemberDeclaration
    implements JFieldDeclarationType
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    protected JmlFieldDeclaration( TokenReference where, 
				   JmlVarAssertion[] varAssertions,
				   JmlDataGroupAccumulator dataGroups,
				   JFieldDeclaration delegee ) 
    {
	super( where, delegee );
        this.varAssertions = varAssertions;
	if (dataGroups == null) {
	    inGroups = new JmlInGroupClause[0];
	    mapsIntoGroups = new JmlMapsIntoClause[0];
	} else {
	    inGroups = dataGroups.inGroupClauses();
	    mapsIntoGroups = dataGroups.getMapsIntoClausesFor(delegee.ident());
	}
	this.delegee = delegee;
    }
    
    public static JmlFieldDeclaration 
	makeInstance( TokenReference where, JVariableDefinition var,
		      JavadocComment javadoc, JavaStyleComment[] comment,
		      JmlVarAssertion[] varAssertions,
		      JmlDataGroupAccumulator dataGroups)
    {
	JFieldDeclaration delegee 
	    = new JFieldDeclarationWrapper( where, var, javadoc, comment );
	return new JmlFieldDeclaration( where, varAssertions, 
					dataGroups, delegee );
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * Indicates whether this field declaration has an accompanying
     * jml-var-assertion.  
     *
     * <pre><jml>
     * ensures \result <==> varAssertions != null && varAssertions.length > 0;
     * </jml></pre>
     */
    public /*@ pure @*/ boolean hasAssertions() {
	return varAssertions != null && varAssertions.length > 0;
    }

    /**
     * Returns the jml-var-assertion associated with this.
     *
     * <pre><jml>
     * requires hasAssertions();
     * </jml></pre>
     *
     */
    public /*@ pure @*/ JmlVarAssertion[] varAssertions() {
	return varAssertions;
    }

    /**
     * Returns true if this field declarator has an initializer (should
     * be initialized) */
    public /*@ pure @*/ boolean hasInitializer() {
	return delegee.hasInitializer();
    }

    /**
     * @return	the value of this field at initialization
     */
    public /*@ pure @*/ JExpression getInitializer() {
	return delegee.getInitializer();
    }

    /**
     * Sets the initialization expression for this field.
     */
    public void setInitializer(JExpression expr) {

	delegee.setInitializer(expr);
    }

    /**
     * Returns the field declaration in the refinement chain that has an 
     * initializer. 
     * 
     */
    public JmlFieldDeclaration findDeclWithInitializer() {
	if (hasInitializer()) {
	    return this;
	} else {
	    JmlMemberDeclaration refField = this.getRefinedMember();
	    return ( !(refField instanceof JmlFieldDeclaration) ? 
		     null 
		     : ((JmlFieldDeclaration)refField).findDeclWithInitializer()
		     );
	}
    }

    /**
     * Returns the type of this field
     */
    public /*@ pure @*/ CType getType() {
	return delegee.getType();
    }

    /**
     * Set the nullity status of this declarator.
     */
    public void setNonNull() {
	delegee.setNonNull();
    }

    /**
     * Returns true if this field need to be initialized WARNING: this
     * method returns true when initial value corresponds to a default
     * value ====> a second check should be made after typecheck
     * to ensure that an initialization is really needed */
    public /*@ pure @*/ boolean needInitialization() {
	return delegee.needInitialization();
    }


    public /*@ pure @*/ JVariableDefinition variable() {
	return delegee.variable();
    }

    /** Returns the modifiers of this field declaration */
    public /*@ pure @*/ long modifiers() {
	return delegee.variable().modifiers();
    }

    /** Set the modifiers of this field declaration. */
    public void setModifiers(long mod) {
	delegee.variable().setModifiers(mod);
    }

   /** Returns the identifier of this field declaration */
    public /*@ pure @*/ String ident() {
	return delegee.variable().ident();
    }

    /** 
     * Returns the Java source code generated by jmlrac for runtime
     * assertion checking. E.g., initialzer for ghost variables. */
    public /*@ pure @*/ JStatement assertionCode() {
	return assertionCode;
    }

    /** 
     * Returns <code>true</code> if this field declaration has the
     * Java source code generated by jmlrac. E.g., initialzer for
     * ghost variables. */
    public /*@ pure @*/ boolean hasAssertionCode() {
	return assertionCode != null;
    }

    /** 
     * Sets the Java source code generated by jmlrac for runtime
     * assertion checking. E.g., initialzer for ghost variables. */
    public void setAssertionCode(JStatement code) {
	assertionCode = code;
    }

    /**
     * @return	the member access information object for this member.
     */
    public JmlMemberAccess jmlAccess() {
	JmlSourceField self = (JmlSourceField) delegee.getField();
	return self.jmlAccess();
    }

    /**
     * Returns true if this member is declared with a 'model' modifier.
     */
    public boolean isModel() {
	return jmlAccess().isModel();
    }

    // ----------------------------------------------------------------------
    // INTERFACE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Checks the basic interfaces to make sure things generally look OK. 
     * This pass gathers information about the type signatures of everything 
     * (imported class files, classes being compiled, methods, fields, etc...)
     * needed for the later passes.  This information is stored 
     * in a context hierarchy that is bound to the AST.
     *
     * @param context the context in which this field appears
     * @return the signature of this field
     * @exception PositionedError an error with reference to the source file
     */
    public CSourceField checkInterface(CClassContextType context) 
	throws PositionedError  
    {
	// This is where the links between the AST and the signature 
	// objects are created (in both directions).  
	JmlSourceField field 
	    = (JmlSourceField) delegee.checkInterface( context );
	field.setAST(this);
	return field;
    }

    // ----------------------------------------------------------------------
    // CODE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Checks whether this field declaration includes a field
     * initializer and mutates the context to store this information
     * about the field.  Records the value of a compile-time constant
     * initializer.
     *
     * @param	context	the context in which this field is declared
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError 
    {
	try {
	    enterSpecScope(modifiers());

	    // delegate to the Java typechecker
	    delegee.typecheck( context );
	    
	    // do JML-specific typechecking after delegation
	    JmlSourceField self = (JmlSourceField) delegee.getField();
	    
	    if(self.isGhost()){
	    	//          no support in AspectJML --- [[[hemr]]]
	    	check(context, 
	    			false,
	    			JmlMessages.NO_SUPPORT_GHOST_FIELD_STATEMENT);
	    }

	    if ( self.isModel() ) {
		// make sure that model fields do not have an initializer
	    	if(self.isStatic()){
	    		if(self.owner().isInterface()){
//	              no support in AspectJML --- [[[hemr]]]
			    	check(context, 
			    			false,
			    			JmlMessages.NO_SUPPORT_STATIC_MODEL_FIELD_ON_INTERFACE);
	    		}
	    	}
		check( context,
		       ! hasInitializer(),
		       JmlMessages.MODEL_FIELD_WITH_INITIALIZER );
	    } else if ( self.isGhost() ) {
		// make sure there is only one initializer defined for this 
		// field 
		if (this.isRefiningMember()) {
		    JmlMemberDeclaration refField = this.getRefinedMember();
		    if (refField instanceof JmlFieldDeclaration) {
			check(context,
			      ((JmlFieldDeclaration)refField)
			      .findDeclWithInitializer() == null,
			      JmlMessages.FIELD_WITH_MORE_THAN_ONE_INITIALIZER,
			      this.stringRepresentation() );
		    }
		}
	    } else {
		// make sure that the initializer of non-model fields only 
		// occur in a '.java' file.
		if (hasInitializer()) {
		    check( context,
			   self.inJavaFile(),
			   JmlMessages.FIELD_INIT_NOT_IN_JAVA_FILE );
		}
	    }

	    // monitored: only for non-static fields
	    if (hasFlag(modifiers(), ACC_MONITORED)) {
		check(context, 
		      !hasFlag(modifiers(), ACC_STATIC),
		      JmlMessages.MONITORED_FOR_STATIC);
	    }
	    checkNullityAdjustType(context);
	    checkRefinementConsistency(context);
	    checkAdmissibility(context);
	    checkFieldSpecs( context, self );
	    getValueOfStaticFieldFromClass(context);
	    accumulateNonNullStats(context);
	}
	finally {
	    exitSpecScope(modifiers());
	}
    }

    /** 
     * Ensures that at most one nullity modifier is used and that it
     * is applied to a reference type.  Also set the type of this
     * class member to non-null if appropriate.
     */
    private void checkNullityAdjustType(CContextType context) throws PositionedError
    {
	// Check for proper use of nullity modifiers and adjust the type, if necessary.
	if( getType().isReference() ) {
	    // getType().isReference() ==> getType() instanceof CClassType
	    CClassType type = (CClassType) getType();

	    // Set nullity qualifier of the type of this, if necessary.
	    if(hasFlag(modifiers(), ACC_NON_NULL)) {
		setNonNull();
	    } else if(!hasFlag(modifiers(), ACC_NULLABLE)) {
		// No explicit nullity modifier is present
		CClass clazz = context.getClassContext().getHostClass();
		if(Main.jmlOptions == null) {
		    throw new IllegalStateException("Main.jmlOptions should not be null");
		}
		if(hasFlag(clazz.access().modifiers(), ACC_NON_NULL_BY_DEFAULT)
		   || !hasFlag(clazz.access().modifiers(), ACC_NULLABLE_BY_DEFAULT)
		   && Main.jmlOptions.defaultNonNull()) {
		    setNonNull();
		}
	    }
	} else {
	    // There should be no nullity modifiers.
	    check(context, 
		  !hasFlag(modifiers(), NULLITY_MODS),
		  JmlMessages.NULLITY_MODIFIERS_FOR_NON_REF_TYPE,
		  new Object[] { CTopLevel.getCompiler().modUtil()
				 .asString(modifiers() & NULLITY_MODS).trim(), 
				 getType() });
	}
    }

    /** Admissibility check:
     * if ownership admissibility checks are enabled,
     * one must check that if a non-model field is not declared private, then its
     * type is not declared as rep, i.e. a non-model rep field must be private.
     */
    private void checkAdmissibility(CContextType context) throws PositionedError 
    {
	JmlSourceField self = (JmlSourceField) delegee.getField();
	// Method body by rzakhejm
	if (JmlAdmissibilityVisitor.isAdmissibilityOwnershipEnabled()) {
	    if (!hasFlag(modifiers(), ACC_PRIVATE) && !hasFlag(modifiers(), ACC_MODEL) && self.getType().isClassType() &&
		(((CClassType) self.getType()).getCUniverse() instanceof CUniverseRep)) {
		warn(context, JmlMessages.NOT_ADMISSIBLE_REP_FIELD_PRIVATE);
	    }
	}
    }

    /** Get the value of a static (final) field from its class (since
     * this value cannot be obtained from the class spec).
     */
    private void getValueOfStaticFieldFromClass(CContextType context) 
    {
	// Fix by Hao Xi:
	// process public static and final field: get value from corresponding class
	// I suspect that we don't really need to restrict it to public fields
	// (it could be protected).
	if ((delegee.variable().modifiers()==(ACC_PUBLIC |ACC_STATIC |ACC_FINAL))&&(!isModel())){
	    String qName = delegee.variable().getTokenReference().file().getPath();
	    qName = qName.replace('\\','/'); //if on windows , replace "\" with "/"
	    if (qName.indexOf(".")!=-1) { // remove extention name
		qName=qName.substring(0,qName.indexOf("."));
	    }
	    while (qName.indexOf("/")!=-1){
		CClassType outerType;
		try {
		    outerType = CTopLevel.getTypeRep(qName, true);
		    outerType.checkType(context);
		    CClass outer = outerType.getCClass();
		    if (outer!=null) break;
		} catch (UnpositionedError ue) {
		    if (qName.indexOf("/")!=-1)
			qName=qName.substring(qName.indexOf("/")+1,qName.length());
		    else //cannot find any class
			throw new RuntimeException("Can not find any class with name "+qName);
		}
	    }
	    try{
		ClassInfo cf = ClassPath.getClassInfo(qName, true);		   
		if (cf!=null){
		    FieldInfo[]fields = cf.getFields();
		    for (int i = 0; i < fields.length; i++) {
			if (fields[i].getName().compareTo(ident())==0) {
			    Object value = fields[i].getConstantValue();
			    if (value!=null){
				JLiteral js= JLiteral.createLiteral(getType(), value);
				if (js!=null) setInitializer(js);
			    }
			}
		    }
		}

	    } catch (ClassFileReadException e) {
		CTopLevel.getCompiler().inform(e);
	    }
	}
    }

    /**
     * Typechecks the specifications associated with this 
     * field, i.e., data group specifications.  
     *
     * @param	context	the context in which this field is declared
     * @exception PositionedError if any checks fail */
    public void checkFieldSpecs( CFlowControlContextType context,
				 JmlSourceField self ) 
	throws PositionedError 
    {
	JmlFieldSpecsContext specCtx = new JmlFieldSpecsContext(context);
	if (varAssertions != null) {
	    for (int i = 0; i < varAssertions.length; i++) {
		varAssertions[i].typecheck( specCtx );
	    }
	}

	long privacy = self.jmlAccess().privacy();
	int i;
	for (i=0; i<inGroups.length; i++) {
	    inGroups[i].typecheck( specCtx, privacy );
	    JmlInGroupClause g = inGroups[i];
	    JmlSourceField[] sf = g.getDataGroups((JmlSourceField)getField());
	    for (int k=0; k<sf.length; ++k) {
		// FIXME - here and below.  I'm not quite sure of the 
		// circumstances under which sf[k] might be null.  In other
		// places it says that the typechekcing is not complete.  If
		// that is so, is this work to initialize datagroupContents
		// correct?
		if (sf[k] != null) {
		    JmlMemberDeclaration md = sf[k].getAST();
		    if (md instanceof JmlFieldDeclaration) {
			((JmlFieldDeclaration)md).datagroupContents.add(this);
		    } else {
			System.out.println("JMLFD " + md.getClass());
		    }
		}
	    }
	}
	if ( this.isModel() ) {
	    // model fields are not allowed to have maps clauses
	    // since they to not have concrete fields!
	    check( context,
		   mapsIntoGroups.length == 0, 
		   JmlMessages.INVALID_MAPS_CLAUSE, 
		   delegee.ident() );
	} else {
	    // check the maps clauses
	    for (i=0; i<mapsIntoGroups.length; i++) {
		mapsIntoGroups[i].typecheck( specCtx, privacy );
		JmlMapsIntoClause g = mapsIntoGroups[i];
		JmlSourceField[] sf 
		    = g.getDataGroups((JmlSourceField)getField());
		for (int k=0; k<sf.length; ++k) {
		    if (sf[k] != null) {
			JmlMemberDeclaration md = sf[k].getAST();
			if (md instanceof JmlFieldDeclaration) {
			    ((JmlFieldDeclaration)md).datagroupContents
				.add(g.memberRef());
			} else {
			    System.out.println("JMLFD " + md.getClass());
			}
		    }
		}
	    }
	}
    }

    private void accumulateNonNullStats(CContextType context) 
	throws PositionedError
    {
//	if (Main.jmlOptions.nonnull()) {
//	    long fieldMods = delegee.variable().modifiers();
//	    if (NonNullStatistics.hmArgs.containsKey(
//						     Utils.getFilePath(getTokenReference().file()))) {
//		String hci = context instanceof JmlContext 
//		    ? ((JmlContext) context).getHostClass().ident() 
//		    : "NOT-JML-CONTEXT";
//		String str =Utils.getFilePath(getTokenReference().file())
//		    +"|"+hci
//		    +"|"+ident();
//		//System.out.println("in jmlfielddecl,str is  "+str);
//		// if hmNonnull contains key already, 
//		//      it is has been put into hm, check invariant static ?
//		if (NonNullStatistics.hmNonnull.containsKey(str)){
//		    if (hasFlag( fieldMods, ACC_STATIC)) {
//			//static
//			if (((String)NonNullStatistics.
//			     hmNonnull.get(str)).compareTo("sf")==0) {
//			    // in static invariant
//			    NonNullStatistics.hmNnStat.put(str,"Nf");
//			}
//		    } else {// not static
//			if (((String)NonNullStatistics.
//			     hmNonnull.get(str)).compareTo("if")==0) {
//			    // in non-static invariant
//			    NonNullStatistics.hmNnStat.put(str,"Nf");
//			}
//		    }
//		}
//
//		if (hasFlag( fieldMods, ACC_NON_NULL)) {
//		    if (hasFlag( fieldMods, ACC_MODEL)){
//			//Model and Non null
//			NonNullStatistics.hmNonnullPut(str,"Mf");
//		    }else if (hasFlag(fieldMods, ACC_GHOST)) {
//			//Ghost and Non null
//			NonNullStatistics.hmNonnullPut(str,"Gf");
//		    } else {
//			//non null
//			NonNullStatistics.hmNonnullPut(str,"Rf");
//		    }
//		} else if (delegee.isDeclaredNonNull()
//			   /* hasFlag(context.getClassContext().
//				   getHostClass().access().modifiers(),
//				   Constants.ACC_NON_NULL_BY_DEFAULT)
//			   && !hasFlag(fieldMods, ACC_NULLABLE)
//			   */ ) {
//		    //take it as implicit non_null
//		    NonNullStatistics.hmNnStat.put(str,"Nf");
//		    if (hasFlag( fieldMods, ACC_MODEL)
//			&& delegee.variable().getType().isReference()) {
//			//Model
//			NonNullStatistics.hmNonnullPut(str,"mf");
//			if (hasFlag(fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"ms");
//			}
//                    } else if (hasFlag( fieldMods, ACC_GHOST)
//			       && delegee.variable().getType().isReference()) {
//			// Ghost
//                        NonNullStatistics.hmNonnullPut(str,"gf");
//			if (hasFlag( fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"gs");
//			}
//                    } else if (delegee.variable().getType().isReference()) {
//			//System.out.println("in field decl, put str in hm "+str);			
//			//reference var
//                        NonNullStatistics.hmNonnullPut(str,"rf");
//			if (hasFlag( fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"rs");
//			}
//		    }
//		} else {
//		    if (hasFlag( fieldMods, ACC_MODEL)
//			&& delegee.variable().getType().isReference()) {
//			//Model
//			NonNullStatistics.hmNonnullPut(str,"mf");
//			if (hasFlag( fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"ms");
//			}
//		    } else if (hasFlag( fieldMods, ACC_GHOST)
//			       && delegee.variable().getType().isReference()) {
//			// Ghost
//			NonNullStatistics.hmNonnullPut(str,"gf");
//			if (hasFlag( fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"gs");
//			}
//		    }else if (delegee.variable().getType().isReference()){
//			//System.out.println("in field decl, put str in hm "+str);			
//			//reference var
//			NonNullStatistics.hmNonnullPut(str,"rf");
//			if (hasFlag( fieldMods, ACC_STATIC)) {
//			    NonNullStatistics.hmNonnullPut(str,"rs");
//			}
//		    }
//		}
//
//		if (hasFlag( fieldMods, ACC_FINAL)
//		    && delegee.variable().getType().isReference()
//		    && hasInitializer()) {
//		    //static final field
//		    if (!(getInitializer().isLiteral()
//			  && (getInitializer().getLiteral() instanceof 
//			      JNullLiteral))) {
//			//non null, like ="a";
//			NonNullStatistics.hmNnStat.put(str,"Nf");
//		    }
//		}
//	    }
//	}

    }

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
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlFieldDeclaration(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // INNER CLASS
    //---------------------------------------------------------------------

    /** A special flow control context class for typechecking JML 
     * data group clauses. The declared field is assumed to 
     * be initialized and the typechecking result is not propagated to
     * the parent context.
     */
    class JmlFieldSpecsContext extends CFlowControlContext {
        JmlFieldSpecsContext(CFlowControlContextType parent) {
            super(parent,JmlFieldDeclaration.this.getTokenReference());
            // assume the declared field initialized.
            initializeField(
		((CSourceField) JmlFieldDeclaration.this.getField()));
        }

        /** This method is overridden here so as not to propagate
         * typechecking result to the parent context, specifically 
	 * the assumption that the field has been initialized. 
	 */
        public void checkingComplete() {
        }
    }

    //---------------------------------------------------------------------
    // REFINEMENT
    //---------------------------------------------------------------------

    public void checkRefinementConsistency(CContextType context)
	throws PositionedError 
    {
	JmlSourceField self = (JmlSourceField) delegee.getField();
	if ( this.isRefiningMember() ) {
	    // Check the modifiers common to methods and fields
	    JmlMemberAccess selfAccess = this.jmlAccess();
	    checkRefinedModifiers(context, this);

	    JmlSourceField refinedSrcField 
		= (JmlSourceField) refinedDecl.getField();
	    JmlMemberAccess refinedAccess = refinedSrcField.jmlAccess();
	    String thisStringRep = this.stringRepresentation();

	    CClass refinedOwner = refinedSrcField.owner();
	    java.io.File refinedFile = refinedOwner.sourceFile();
	    String refinedFileName = refinedFile.getName();
	    Object msgArgs[] = new Object[4];
	    msgArgs[0] = thisStringRep;
	    msgArgs[1] = refinedFileName;
	    msgArgs[2] = refinedSrcField.getType().toString();
	    // check to make sure the types are the same
	    check( context,
		   self.getType().equals(refinedSrcField.getType()),
		   JmlMessages.DIFFERENT_REFINING_FIELD_TYPE, 
		   msgArgs  );

	    // Check the Java field modifiers
	    // selfAccess.isTransient() <==> refinedAccess.isTransient()
	    if ( selfAccess.isTransient() ) {
		msgArgs[0] = "Transient";
		msgArgs[2] = "non-transient";
		check( context,
		       refinedAccess.isTransient(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-transient";
		msgArgs[2] = "transient";
		check( context,
		       !refinedAccess.isTransient(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // selfAccess.isVolatile() <==> refinedAccess.isVolatile()
	    if ( selfAccess.isVolatile() ) {
		msgArgs[0] = "Volatile";
		msgArgs[2] = "non-volatile";
		check( context,
		       refinedAccess.isVolatile(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-volatile";
		msgArgs[2] = "volatile";
		check( context,
		       !refinedAccess.isVolatile(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }

	    // Check the JML field modifiers
	    // selfAccess.isGhost() <==> refinedAccess.isGhost()
	    if ( selfAccess.isGhost() ) {
		msgArgs[0] = "Ghost";
		msgArgs[2] = "non-ghost";
		check( context,
		       refinedAccess.isGhost(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-ghost";
		msgArgs[2] = "ghost";
		check( context,
		       !refinedAccess.isGhost(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // selfAccess.isInstance() <==> refinedAccess.isInstance()
	    if ( selfAccess.isInstance() ) {
		msgArgs[0] = "Instance";
		msgArgs[2] = "non-instance";
		check( context,
		       refinedAccess.isInstance(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-instance";
		msgArgs[2] = "instance";
		check( context,
		       !refinedAccess.isInstance(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // selfAccess.isUninitialized() <==> refinedAccess.isUninitialized()
	    if ( selfAccess.isUninitialized() ) {
		msgArgs[0] = "Uninitialized";
		msgArgs[2] = "initialized";
		check( context,
		       refinedAccess.isUninitialized(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Initialized";
		msgArgs[2] = "uninitialized";
		check( context,
		       !refinedAccess.isUninitialized(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	    // selfAccess.isMonitored() <==> refinedAccess.isMonitored()
	    if ( selfAccess.isMonitored() ) {
		msgArgs[0] = "Monitored";
		msgArgs[2] = "non-monitored";
		check( context,
		       refinedAccess.isMonitored(), 
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Non-monitored";
		msgArgs[2] = "monitored";
		check( context,
		       !refinedAccess.isMonitored(), 
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
		       !(refinedSrcField.getType().isReference()
			 && !refinedSrcField.isDeclaredNonNull()),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    } else {
		msgArgs[0] = "Nullable";
		msgArgs[2] = "non-null";
		check( context,
		       !(getType().isReference()
			 && refinedSrcField.getType().isReference()
			 && refinedSrcField.isDeclaredNonNull()),
		       JmlMessages.INVALID_REFINING_MODIFIER, 
		       msgArgs  );
	    }
	}
    }

    /**
     * Determines the field refined by this field (if there is one).  
     * Caches the result for later calls to 
     * {@link #getRefinedMember()}.
     * Also links the refined field back to this, 
     * so they are linked to each other.
     */
    protected void setRefinementLinks() {
	JmlSourceField self = (JmlSourceField) getField(); 
	if (refinedDecl == null) {
	    // has NOT already been set

	    // compute and then set the refined field
	    JmlSourceClass ownerClass = (JmlSourceClass) self.owner();
	    JmlSourceField refinedSrc = ownerClass.lookupRefinedField(self);
	    if (refinedSrc != null) {
		JmlMemberDeclaration refinedField = refinedSrc.getAST();
		refinedDecl = refinedField;
		refinedField.setRefiningMember(this);
	    }
	}
    }

    protected void setRefiningField(JmlFieldDeclaration refiningField) {
	refiningDecl = refiningField;
    }

    //---------------------------------------------------------------------
    // COMBINE SPECIFICATIONS
    //---------------------------------------------------------------------

    public void setSpecstoCombinedSpecs() {
	this.inGroups = combinedInGroups;
	this.mapsIntoGroups = combinedMapsIntoGroups;
	this.varAssertions = combinedVarAssertions;
    }

    /**
     *  Returns the variable assertions of this member declaration 
     *  combined with the assertions of those it refines.
     *  Returns null if it does not have any combined variable assertions.
     */
    public /*@ pure @*/ JmlVarAssertion[] getCombinedVarAssertions() {
	return combinedVarAssertions;
    }
    
    public void combineSpecifications() 
    {
	if (combinedVarAssertions == null) {
	    if (this.isRefiningMember()) {
		JmlMemberDeclaration refField = this.getRefinedMember();
		if (refField instanceof JmlFieldDeclaration) {
		    // combine specs of the refined field declaration
		    refField.combineSpecifications();
		    JmlVarAssertion[] refVarAssertions 
			= refField.getCombinedVarAssertions();
		    combinedVarAssertions = (JmlVarAssertion[]) Utils 
			.combineArrays(refVarAssertions, varAssertions);
		    combineDataGroups((JmlFieldDeclaration)refField);
		} else {
		    // this is the case where the refined file is a .class file
		    combinedVarAssertions = varAssertions;
		    combinedInGroups = this.inGroups;
		    combinedMapsIntoGroups = this.mapsIntoGroups;
		}
	    } else {
		// this is the case where this declaration is the least 
		// refined file in the refinement chain
		combinedVarAssertions = varAssertions;
		combinedInGroups = this.inGroups;
		combinedMapsIntoGroups = this.mapsIntoGroups;
	    }
	}
    }

    public void combineDataGroups(JmlFieldDeclaration refField) {
	if (refField == null) {
	    combinedInGroups = this.inGroups;
	    combinedMapsIntoGroups = this.mapsIntoGroups;
	} else {
	    combinedInGroups 
		= refField.getCombinedInGroupClauses();
	    combinedMapsIntoGroups 
		= refField.getCombinedMapsIntoClauses();

	    combinedInGroups = (JmlInGroupClause[]) 
		Utils.combineArrays(combinedInGroups, this.inGroups);
	    combinedMapsIntoGroups = (JmlMapsIntoClause[]) 
		Utils.combineArrays(combinedMapsIntoGroups, 
				    this.mapsIntoGroups);
	}
    }

    public JmlInGroupClause[] inGroupClauses() {
	return inGroups;
    }

    public JmlInGroupClause[] getCombinedInGroupClauses() {
	if (combinedInGroups == null) combineSpecifications();
	return combinedInGroups;
    }

    public JmlMapsIntoClause[] mapsIntoClauses() {
	return mapsIntoGroups;
    }

    public JmlMapsIntoClause[] getCombinedMapsIntoClauses() {
	return combinedMapsIntoGroups;
    }

    public void addToDataGroups( JmlDataGroupMemberMap dataGroupMap ) {
	JmlSourceField self = (JmlSourceField) getField(); 
	this.combineSpecifications();
	if (combinedInGroups != null) {
	    for (int i=0; i<combinedInGroups.length; i++) {
		if ( !combinedInGroups[i].isRedundantly() ) {
		    addSelfToInDataGroups( self, 
					   combinedInGroups[i], 
					   dataGroupMap );
		}
	    }
	}
    }

    public void addSelfToInDataGroups( JmlSourceField self,
				       JmlInGroupClause inGroupClause,
				       JmlDataGroupMemberMap dataGroupMap )
    {
	JmlSourceField groups[] = inGroupClause.getDataGroups( self );
	for (int i=0; i<groups.length; i++) {
	    if (groups[i] != null) {
		dataGroupMap.addMember( groups[i], self);
	    } else {
		/*
		    System.err.println("Group " + groupNames[i] 
				   + " not typechecked before the call to"
				   + " JmlFieldDeclaration.addToDataGroups()");
		 */
	    }
	}
    }
    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ spec_public @*/ private JmlVarAssertion[] varAssertions;
    /*@ spec_public @*/ private JmlVarAssertion[] combinedVarAssertions = null;

    private JmlInGroupClause[] inGroups = null;
    private JmlInGroupClause[] combinedInGroups = null;

    private JmlMapsIntoClause[] mapsIntoGroups = null;
    private JmlMapsIntoClause[] combinedMapsIntoGroups = null;

    public ArrayList datagroupContents = new ArrayList(); // JmlSpecRefExpression
    private JFieldDeclaration delegee;

    /** Java source code generated by jmlrac for runtime assertion
     * checking. E.g., initialzer for ghost variables. */
    private JStatement assertionCode;

}// JmlFieldDeclaration
