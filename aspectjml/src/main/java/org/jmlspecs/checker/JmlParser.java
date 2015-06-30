// $ANTLR 2.7.7 (20070227): "expandedJml.g" -> "JmlParser.java"$

/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler, and the JML project.
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
 * $Id: Jml.g,v 1.141 2007/04/18 23:04:37 leavens Exp $
 */


    // common parser/lexer header
    package org.jmlspecs.checker;

    import java.util.ArrayList;

import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.CArrayType;
import org.multijava.mjc.CBooleanValueType;
import org.multijava.mjc.CClassType;
import org.multijava.mjc.COrdinalValueType;
import org.multijava.mjc.CParseCompilationUnitContext;
import org.multijava.mjc.CRealValueType;
import org.multijava.mjc.CSpecializedType;
import org.multijava.mjc.CStdType;
import org.multijava.mjc.CStringValueType;
import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.CType;
import org.multijava.mjc.CTypeVariable;
import org.multijava.mjc.CUniverse;
import org.multijava.mjc.CUniverseImplicitPeer;
import org.multijava.mjc.CUniverseImplicitReadonly;
import org.multijava.mjc.CUniverseMessages;
import org.multijava.mjc.CUniversePeer;
import org.multijava.mjc.CUniverseReadonly;
import org.multijava.mjc.CUniverseRep;
import org.multijava.mjc.CWildcardType;
import org.multijava.mjc.JArrayAccessExpression;
import org.multijava.mjc.JArrayDimsAndInits;
import org.multijava.mjc.JArrayInitializer;
import org.multijava.mjc.JAssertStatement;
import org.multijava.mjc.JAssignmentExpression;
import org.multijava.mjc.JBlock;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JBreakStatement;
import org.multijava.mjc.JCastExpression;
import org.multijava.mjc.JCatchClause;
import org.multijava.mjc.JCharLiteral;
import org.multijava.mjc.JClassDeclarationType;
import org.multijava.mjc.JClassExpression;
import org.multijava.mjc.JClassOrGFImportType;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JConditionalExpression;
import org.multijava.mjc.JConditionalOrExpression;
import org.multijava.mjc.JContinueStatement;
import org.multijava.mjc.JDoStatement;
import org.multijava.mjc.JEmptyStatement;
import org.multijava.mjc.JExplicitConstructorInvocation;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JExpressionFactory;
import org.multijava.mjc.JExpressionListStatement;
import org.multijava.mjc.JExpressionStatement;
import org.multijava.mjc.JForStatement;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JIfStatement;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JInterfaceDeclarationType;
import org.multijava.mjc.JLabeledStatement;
import org.multijava.mjc.JLocalVariable;
import org.multijava.mjc.JLoopStatement;
import org.multijava.mjc.JMethodCallExpression;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNewAnonymousClassExpression;
import org.multijava.mjc.JNewArrayExpression;
import org.multijava.mjc.JNewObjectExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JOrdinalLiteral;
import org.multijava.mjc.JPackageName;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JPostfixExpression;
import org.multijava.mjc.JPrefixExpression;
import org.multijava.mjc.JRealLiteral;
import org.multijava.mjc.JResendExpression;
import org.multijava.mjc.JReturnStatement;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.JStringLiteral;
import org.multijava.mjc.JSuperExpression;
import org.multijava.mjc.JSwitchGroup;
import org.multijava.mjc.JSwitchLabel;
import org.multijava.mjc.JSwitchStatement;
import org.multijava.mjc.JSynchronizedStatement;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JThrowStatement;
import org.multijava.mjc.JTryCatchStatement;
import org.multijava.mjc.JTryFinallyStatement;
import org.multijava.mjc.JTypeDeclarationStatement;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JVariableDeclarationStatement;
import org.multijava.mjc.JVariableDefinition;
import org.multijava.mjc.JWhileStatement;
import org.multijava.mjc.MJMathModeExpression;
import org.multijava.mjc.MJTopLevelMethodDeclaration;
import org.multijava.mjc.MJWarnExpression;
import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.ParserUtility;
import org.multijava.mjc.ParsingController;
import org.multijava.util.Utils;
import org.multijava.util.compiler.CWarning;
import org.multijava.util.compiler.JavaStyleComment;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

import antlr.ANTLRException;
import antlr.NoViableAltException;
import antlr.ParserSharedInputState;
import antlr.RecognitionException;
import antlr.SemanticException;
import antlr.Token;
import antlr.TokenBuffer;
import antlr.TokenStream;
import antlr.TokenStreamException;
import antlr.collections.impl.BitSet;
// Parser class preamble
    

public class JmlParser extends antlr.LLkParser       implements JmlTokenTypes
 {

    public JmlParser( org.multijava.mjc.Main compiler, TokenStream lexer,
        ParsingController parsingController,
        boolean allowGeneric, boolean allowMultiJava,
        boolean allowRelaxedMultiJava,
        boolean allowUniverseKeywords ) // WMD
    {
        this( compiler, lexer, parsingController, allowGeneric,
              allowMultiJava, allowRelaxedMultiJava, allowUniverseKeywords,
              false );
    }

    public JmlParser( org.multijava.mjc.Main compiler, TokenStream lexer,
        ParsingController parsingController, boolean allowGeneric,
        boolean allowMultiJava, boolean allowRelaxedMultiJava,
        boolean allowUniverseKeywords, // WMD
        boolean isRefinedCUnit )
    {
        this( lexer );
        this.utility =
        new JmlParserUtility( compiler, parsingController, allowGeneric,
            allowMultiJava, allowRelaxedMultiJava, allowUniverseKeywords, true);
        this.isRefinedCUnit = isRefinedCUnit;
    }

    /**
     * Returns an exception from our exception hierarchy by wrapping
     * the ANTLR excepton.  The exception is really positioned, by the
     * positioning information is embedded in the message. */
    public PositionedError beautifyParserError( ANTLRException e ) {
	return utility.beautifyParserError( e );
    }

    /**
     * Returns true if the argument mod is one of the privacy modifiers
     * (i.e., public, protected or privacy) or null (= 0). */
    public static boolean isPrivacyOrNull(long mod) {
        return (mod == 0 ||
	    mod == Constants.ACC_PUBLIC ||
	    mod == Constants.ACC_PROTECTED ||
	    mod == Constants.ACC_PRIVATE);
    }

    /**
     * Returns true if all elements of the argument are simple spec body
     * clauses; otherwise, print an appropriate error message and
     * return false */
    public boolean verifySimpleSpecBody(JmlSpecBodyClause[] clauses) {
        boolean result = true;
        for (int i = 0; i < clauses.length; i++)
	if (!clauses[i].isSimpleSpecBody()) {
	    utility.reportTrouble( new PositionedError(
                    clauses[i].getTokenReference(),
                    JmlMessages.BAD_SIMPLE_SPEC_BODY ));
	    result = false;
	}
        return result;
    }

    /**
     * Returns true if all elements of the argument are normal spec body
     * clauses; otherwise, print an appropriate error message and
     * return false */
    public boolean verifyNormalSpecBody(JmlSpecBodyClause[] clauses) {
        boolean result = true;
        for (int i = 0; i < clauses.length; i++)
	if (!clauses[i].isNormalSpecBody()) {
	    utility.reportTrouble( new PositionedError(
                    clauses[i].getTokenReference(),
                    JmlMessages.BAD_NORMAL_SPEC_BODY ));
	    result = false;
	}
        return result;
    }

    /**
     * Returns true if all elements of the argument are exceptional spec
     * body clauses; otherwise, print an appropriate error message and
     * return false */
    public boolean verifyExceptionalSpecBody(JmlSpecBodyClause[] clauses) {
        boolean result = true;
        for (int i = 0; i < clauses.length; i++)
	if (!clauses[i].isExceptionalSpecBody()) {
	    utility.reportTrouble( new PositionedError(
                    clauses[i].getTokenReference(),
                    JmlMessages.BAD_EXCEPTIONAL_SPEC_BODY ));
	    result = false;
	}
        return result;
    }

    /**
     * Returns true if all elements of the argument are simple spec
     * statement body clauses; otherwise, print an appropriate error
     * message and return false */
    public boolean verifySimpleSpecStatementBody(JmlSpecBodyClause[] clauses) {
        boolean result = true;
        for (int i = 0; i < clauses.length; i++)
	if (!clauses[i].isSimpleSpecStatementBody()) {
	    utility.reportTrouble( new PositionedError(
                    clauses[i].getTokenReference(),
                    JmlMessages.BAD_SIMPLE_SPEC_STATEMENT_BODY ));
	    result = false;
	}
        return result;
    }

    /**
     * Returns true if all elements of the argument are abrupt spec
     * body clauses; otherwise, print an appropriate error message and
     * return false */
    public boolean verifyAbruptSpecBody(JmlSpecBodyClause[] clauses) {
        boolean result = true;
        for (int i = 0; i < clauses.length; i++)
	if (!clauses[i].isAbruptSpecBody()) {
	    utility.reportTrouble( new PositionedError(
                    clauses[i].getTokenReference(),
                    JmlMessages.BAD_ABRUPT_SPEC_BODY ));
	    result = false;
	}
        return result;
    }

    /**
	 * Generates the appropriate data structure for buffering class
	 * members during parsing.  Implemented as a method for
	 * sub-grammars can use a different data structure (of the same
	 * name).  This is a hack that takes advantage of ANTLR's textual
	 * grammar inheritance.  */
    private CParseClassContext getParseClassContext() {
	// All these "CParseClassContext" refer to the class in the
	// local package (org.jmlspecs.checker).  The casts are
	// needed because the return type of getInstance() is
	// "org.multijava.mjc.CParseClassContext".
	return (CParseClassContext) CParseClassContext.getInstance();
    }

    // --------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    // --------------------------------------------------------------------

	/**
	 * Instances of JmlParser delegate to utility.  */
    private ParserUtility utility;

    private boolean isInModelProgram = false;

    private boolean isRefinedCUnit = false;

    private JExpressionFactory exprFactory = new JmlExpressionFactory();

    private int unmatchedTypeLT = 0 ;
    //---------------------------------------------------------------------
    // NESTED CLASSES
    //---------------------------------------------------------------------

    // !FIXME! The following should be private when Sun fixes its javadoc bug - DRCok
    /*private*/ static class TypeBooleanPair {
	TypeBooleanPair( CClassType type, boolean bool ) {
	    this.type = type;
	    this.bool = bool;
	}
	CClassType type;
	boolean bool;
    }

    /**
	 * This nested class represents a list of implemented interfaces
	 * for a class declaration (or extends interfaces for an interface
	 * declaration) and whether they are implemented (or extended)
	 * weakly.  */
    // !FIXME! The following should be private when Sun fixes its javadoc bug - DRCok
    /*private*/ static class TypeWeaklyList {
	/**
		 * <pre><jml>
		 * model_program {
		 *    weaklyFlags.add( new Boolean( _weakly ) );
		 * }
         * also
		 * assignable weaklyFlags;
		 * </jml></pre>
		 */
	// Note: I'm using _weakly instead of weakly, because
	// weakly is a jml reserved word and causes parsing errors
	void add( CClassType type, boolean _weakly ) {
	    int pos = types.size();
	    types.add( type );
	    if ( _weakly ) {
		if ( indicesSize == indices.length ) {
		    growIndices();
		}
		indices[indicesSize++] = pos;
	    }
	}

	CClassType[] types() {
	    CClassType[] result = new CClassType[ types.size() ];
	    types.toArray( result );
	    return result;
	}

    /**
     * <pre><jml>
     * model_program {
     *    Boolean[] result = new Boolean[ weaklyFlags.size() ];
     *    weaklyFlags.toArray( result );
     *    boolean[] res = new boolean[ weaklyFlags.size() ];
     *    normal_behavior
     *      assignable res;
     *      ensures (\forall int i; 0<=i && i < res.length;
     *                    result[i].booleanValue() == res[i]);
     *    return res;
     * }
     * </jml></pre>
     */
	boolean[] weaklyFlags() {
	    boolean[] result = new boolean[ types.size() ];
	    for ( int i=0; i < indicesSize; i++ ) {
		result[indices[i]] = true;
	    }
	    return result;
	}

	//@  assignable weaklyFlags;
	private void growIndices() {
	    int[] newIndices = new int[ indices.length * 2 ];
	    System.arraycopy( indices, 0, newIndices, 0, indices.length );
	    indices = newIndices;
	}

	private ArrayList types = new ArrayList();

	/*@ protected model ArrayList weaklyFlags;
	  @ initially weaklyFlags.equals( new ArrayList() ); @*/

        /*@ 
		  @ private represents weaklyFlags \such_that
		  @    (\forall int i; 0<=i && i<weaklyFlags.size();
		  @              ((Boolean) weaklyFlags.get(i)).booleanValue() <==>
		  @                     (\exists int j; 0<=j && j<indicesSize;
		  @								 indices[j] == i ));
		  @ private represents_redundantly weaklyFlags \such_that
		  @    (\forall int i; 0<=i && i<indicesSize;
		  @        ((Boolean) weaklyFlags.get(indices[i])).booleanValue() );
		  @ private invariant
		  @    indices != null &&
		  @    indices.length > 0 &&
		  @	   0 <= indicesSize &&
		  @    indicesSize <= indices.length &&
		  @    indicesSize <= types.size();
		  @
		  @*/

	private int[] indices = new int[10];
    //@                in weaklyFlags;

	private int indicesSize = 0;
    //@                in weaklyFlags;

    }


protected JmlParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public JmlParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected JmlParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public JmlParser(TokenStream lexer) {
  this(lexer,2);
}

public JmlParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
}

	public final JCompilationUnitType  jCompilationUnit(
		
	) throws RecognitionException, TokenStreamException {
		JCompilationUnitType self = null;
		
		
		JPackageName pack = JPackageName.UNNAMED;
		JmlRefinePrefix refinePrefix = null;
		JmlRefinePrefix rp2 = null;
		TokenReference sourceRef = utility.buildTokenReference();
		CParseCompilationUnitContext context =
		CParseCompilationUnitContext.getInstance();
		
		// automatic import of package 'org.jmlspecs.lang'
		
		context.addPackageImport(JmlCompilationUnit.JMLSPECS_LANG);
		
		
		{
		switch ( LA(1)) {
		case LITERAL_package:
		{
			pack=jPackageDefinition();
			break;
		}
		case EOF:
		case LITERAL_abstract:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_class:
		case LITERAL_double:
		case LITERAL_final:
		case LITERAL_float:
		case LITERAL_import:
		case LITERAL_int:
		case LITERAL_interface:
		case LITERAL_long:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_pure:
		case LITERAL_short:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_void:
		case LITERAL_volatile:
		case SEMI:
		case IDENT:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_method:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_refine:
		case LITERAL_refines:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			context.setPackage(pack);
		}
		{
		switch ( LA(1)) {
		case LITERAL_refine:
		case LITERAL_refines:
		{
			refinePrefix=jmlRefinePrefix();
			{
			switch ( LA(1)) {
			case LITERAL_refine:
			case LITERAL_refines:
			{
				rp2=jmlRefinePrefix();
				break;
			}
			case EOF:
			case LITERAL_abstract:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_class:
			case LITERAL_double:
			case LITERAL_final:
			case LITERAL_float:
			case LITERAL_import:
			case LITERAL_int:
			case LITERAL_interface:
			case LITERAL_long:
			case LITERAL_native:
			case LITERAL_private:
			case LITERAL_protected:
			case LITERAL_public:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_pure:
			case LITERAL_short:
			case LITERAL_static:
			case LITERAL_strictfp:
			case LITERAL_synchronized:
			case LITERAL_transient:
			case LITERAL_void:
			case LITERAL_volatile:
			case SEMI:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_also:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_behavior:
			case LITERAL_behaviour:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_code:
			case LITERAL_code_bigint_math:
			case LITERAL_code_java_math:
			case LITERAL_code_safe_math:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exceptional_behavior:
			case LITERAL_exceptional_behaviour:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_extract:
			case LITERAL_forall:
			case LITERAL_for_example:
			case LITERAL_ghost:
			case LITERAL_helper:
			case LITERAL_implies_that:
			case LITERAL_instance:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_method:
			case LITERAL_model:
			case LITERAL_model_program:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_monitored:
			case LITERAL_non_null:
			case LITERAL_non_null_by_default:
			case LITERAL_normal_behavior:
			case LITERAL_normal_behaviour:
			case LITERAL_nullable:
			case LITERAL_nullable_by_default:
			case LITERAL_old:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_query:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_secret:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_spec_bigint_math:
			case LITERAL_spec_java_math:
			case LITERAL_spec_protected:
			case LITERAL_spec_public:
			case LITERAL_spec_safe_math:
			case LITERAL_uninitialized:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			case LCURLY_VBAR:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				if (rp2 != null)
						throw
						new TokenStreamException(
						    "A compilation unit may have at most one refine clause." );
					
			}
			break;
		}
		case EOF:
		case LITERAL_abstract:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_class:
		case LITERAL_double:
		case LITERAL_final:
		case LITERAL_float:
		case LITERAL_import:
		case LITERAL_int:
		case LITERAL_interface:
		case LITERAL_long:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_pure:
		case LITERAL_short:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_void:
		case LITERAL_volatile:
		case SEMI:
		case IDENT:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_method:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		{
		_loop7:
		do {
			if ((LA(1)==LITERAL_import||LA(1)==LITERAL_model) && (LA(2)==LITERAL_import||LA(2)==IDENT)) {
				jImportDefinition(context);
			}
			else {
				break _loop7;
			}
			
		} while (true);
		}
		}
		{
		_loop9:
		do {
			if ((_tokenSet_0.member(LA(1)))) {
				mjTopLevelDefinition(context);
			}
			else {
				break _loop9;
			}
			
		} while (true);
		}
		match(Token.EOF_TYPE);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlCompilationUnit(
					sourceRef,
					pack,
					context.compilationUnitExport(),
					context.getPackageImports(),
					context.getSingleImports(),
					context.getTypeDeclarations(),
					context.getMJTopLevelMethodDeclarations(),
					refinePrefix
				    );
				    context.release();
				
		}
		return self;
	}
	
	public final JPackageName  jPackageDefinition(
		
	) throws RecognitionException, TokenStreamException {
		JPackageName self = null;
		
		Token  e = null;
		
		String    name = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LITERAL_package);
		name=jIdentifier();
		e = LT(1);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JPackageName(sourceRef, 
			name, utility.getStatementComment()); 
			utility.flushJavadocTokensWithWarning( e );
			
		}
		return self;
	}
	
	public final JmlRefinePrefix  jmlRefinePrefix(
		
	) throws RecognitionException, TokenStreamException {
		JmlRefinePrefix self = null;
		
		Token  m = null;
		Token  n = null;
		
		ArrayList identList = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_refine:
		{
			match(LITERAL_refine);
			break;
		}
		case LITERAL_refines:
		{
			match(LITERAL_refines);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		m = LT(1);
		match(STRING_LITERAL);
		n = LT(1);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
					utility.flushJavadocTokensWithWarning( n );
					self = new JmlRefinePrefix(
					    utility.buildTokenReference( m ),
					    m.getText()
					);
				
		}
		return self;
	}
	
	public final void jImportDefinition(
		CParseCompilationUnitContext cunit
	) throws RecognitionException, TokenStreamException {
		
		Token  i = null;
		Token  j = null;
		Token  e1 = null;
		
		StringBuffer	buffer = null;
		boolean	star = false;
		boolean isModel = false;
		String	name = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_model:
		{
			match(LITERAL_model);
			if ( inputState.guessing==0 ) {
				isModel = true;
			}
			break;
		}
		case LITERAL_import:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(LITERAL_import);
		i = LT(1);
		match(IDENT);
		{
		_loop15:
		do {
			if ((LA(1)==DOT) && (LA(2)==IDENT)) {
				match(DOT);
				j = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					(buffer ==
							    null ? (buffer = new StringBuffer(i.getText())) : buffer)
							.append('/').append(j.getText());
						
				}
			}
			else {
				break _loop15;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			name = buffer == null ? i.getText() : buffer.toString();
		}
		{
		switch ( LA(1)) {
		case DOT:
		{
			match(DOT);
			match(STAR);
			if ( inputState.guessing==0 ) {
				star = true;
			}
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		e1 = LT(1);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    if (star) {
					cunit.addPackageImport(
					    new JmlPackageImport(sourceRef,
						name, utility.getStatementComment(), isModel));
				    } else {
					JClassOrGFImportType importee =
					new JmlClassOrGFImport(sourceRef,
					    name, utility.getStatementComment(), isModel);
					cunit.addSingleImport( importee );
				    }
				    utility.flushJavadocTokensWithWarning( e1 );
				
		}
	}
	
	public final void mjTopLevelDefinition(
		CParseCompilationUnitContext context
	) throws RecognitionException, TokenStreamException {
		
		
		long mods = 0;                // a bit mask indicating the modifiers  
		Token startToken = LT(1);
		
		
		mods=jModifiers();
		{
		if ((_tokenSet_1.member(LA(1)))) {
			jTypeDefinition(context, mods, startToken);
		}
		else if (((_tokenSet_2.member(LA(1))))&&(utility.allowMultiJava)) {
			mjTopLevelDeclaration(context, mods, startToken);
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
	}
	
	public final long  jModifier(
		
	) throws RecognitionException, TokenStreamException {
		long self = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		{
			self=mjModifier();
			break;
		}
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_extract:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_instance:
		case LITERAL_model:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_query:
		case LITERAL_secret:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		{
			self=jmlModifier();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final long  mjModifier(
		
	) throws RecognitionException, TokenStreamException {
		long self = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_public:
		{
			match(LITERAL_public);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_PUBLIC;
			}
			break;
		}
		case LITERAL_protected:
		{
			match(LITERAL_protected);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_PROTECTED;
			}
			break;
		}
		case LITERAL_private:
		{
			match(LITERAL_private);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_PRIVATE;
			}
			break;
		}
		case LITERAL_static:
		{
			match(LITERAL_static);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_STATIC;
			}
			break;
		}
		case LITERAL_abstract:
		{
			match(LITERAL_abstract);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_ABSTRACT;
			}
			break;
		}
		case LITERAL_final:
		{
			match(LITERAL_final);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_FINAL;
			}
			break;
		}
		case LITERAL_native:
		{
			match(LITERAL_native);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_NATIVE;
			}
			break;
		}
		case LITERAL_synchronized:
		{
			match(LITERAL_synchronized);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_SYNCHRONIZED;
			}
			break;
		}
		case LITERAL_transient:
		{
			match(LITERAL_transient);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_TRANSIENT;
			}
			break;
		}
		case LITERAL_volatile:
		{
			match(LITERAL_volatile);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_VOLATILE;
			}
			break;
		}
		case LITERAL_strictfp:
		{
			match(LITERAL_strictfp);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_STRICT;
			}
			break;
		}
		case LITERAL_pure:
		{
			match(LITERAL_pure);
			if ( inputState.guessing==0 ) {
				self = org.multijava.mjc.Constants.ACC_PURE;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final long  jmlModifier(
		
	) throws RecognitionException, TokenStreamException {
		long self = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_model:
		{
			match(LITERAL_model);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_MODEL;
			}
			break;
		}
		case LITERAL_extract:
		{
			match(LITERAL_extract);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_EXTRACT;
			}
			break;
		}
		case LITERAL_query:
		{
			match(LITERAL_query);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_QUERY;
			}
			break;
		}
		case LITERAL_secret:
		{
			match(LITERAL_secret);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SECRET;
			}
			break;
		}
		case LITERAL_instance:
		{
			match(LITERAL_instance);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_INSTANCE;
			}
			break;
		}
		case LITERAL_spec_public:
		{
			match(LITERAL_spec_public);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SPEC_PUBLIC;
			}
			break;
		}
		case LITERAL_spec_protected:
		{
			match(LITERAL_spec_protected);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SPEC_PROTECTED;
			}
			break;
		}
		case LITERAL_ghost:
		{
			match(LITERAL_ghost);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_GHOST;
			}
			break;
		}
		case LITERAL_monitored:
		{
			match(LITERAL_monitored);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_MONITORED;
			}
			break;
		}
		case LITERAL_uninitialized:
		{
			match(LITERAL_uninitialized);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_UNINITIALIZED;
			}
			break;
		}
		case LITERAL_non_null:
		{
			match(LITERAL_non_null);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_NON_NULL;
			}
			break;
		}
		case LITERAL_nullable:
		{
			match(LITERAL_nullable);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_NULLABLE;
			}
			break;
		}
		case LITERAL_nullable_by_default:
		{
			match(LITERAL_nullable_by_default);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_NULLABLE_BY_DEFAULT;
			}
			break;
		}
		case LITERAL_non_null_by_default:
		{
			match(LITERAL_non_null_by_default);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_NON_NULL_BY_DEFAULT;
			}
			break;
		}
		case LITERAL_helper:
		{
			match(LITERAL_helper);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_HELPER;
			}
			break;
		}
		case LITERAL_code_java_math:
		{
			match(LITERAL_code_java_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_CODE_JAVA_MATH;
			}
			break;
		}
		case LITERAL_code_safe_math:
		{
			match(LITERAL_code_safe_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_CODE_SAFE_MATH;
			}
			break;
		}
		case LITERAL_code_bigint_math:
		{
			match(LITERAL_code_bigint_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_CODE_BIGINT_MATH;
			}
			break;
		}
		case LITERAL_spec_java_math:
		{
			match(LITERAL_spec_java_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SPEC_JAVA_MATH;
			}
			break;
		}
		case LITERAL_spec_safe_math:
		{
			match(LITERAL_spec_safe_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SPEC_SAFE_MATH;
			}
			break;
		}
		case LITERAL_spec_bigint_math:
		{
			match(LITERAL_spec_bigint_math);
			if ( inputState.guessing==0 ) {
				self = Constants.ACC_SPEC_BIGINT_MATH;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CType  jBuiltInType(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_short:
		case LITERAL_void:
		{
			self=mjBuiltInType();
			break;
		}
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		{
			self=jmlBuiltInType();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CType  mjBuiltInType(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		{
			match(LITERAL_boolean);
			if ( inputState.guessing==0 ) {
				self = CStdType.Boolean;
			}
			break;
		}
		case LITERAL_byte:
		{
			match(LITERAL_byte);
			if ( inputState.guessing==0 ) {
				self = CStdType.Byte;
			}
			break;
		}
		case LITERAL_char:
		{
			match(LITERAL_char);
			if ( inputState.guessing==0 ) {
				self = CStdType.Char;
			}
			break;
		}
		case LITERAL_double:
		{
			match(LITERAL_double);
			if ( inputState.guessing==0 ) {
				self = CStdType.Double;
			}
			break;
		}
		case LITERAL_float:
		{
			match(LITERAL_float);
			if ( inputState.guessing==0 ) {
				self = CStdType.Float;
			}
			break;
		}
		case LITERAL_int:
		{
			match(LITERAL_int);
			if ( inputState.guessing==0 ) {
				self = CStdType.Integer;
			}
			break;
		}
		case LITERAL_long:
		{
			match(LITERAL_long);
			if ( inputState.guessing==0 ) {
				self = CStdType.Long;
			}
			break;
		}
		case LITERAL_short:
		{
			match(LITERAL_short);
			if ( inputState.guessing==0 ) {
				self = CStdType.Short;
			}
			break;
		}
		case LITERAL_void:
		{
			match(LITERAL_void);
			if ( inputState.guessing==0 ) {
				self = CStdType.Void;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CType  jmlBuiltInType(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		switch ( LA(1)) {
		case LITERAL_BS_bigint:
		{
			match(LITERAL_BS_bigint);
			if ( inputState.guessing==0 ) {
				self = JmlStdType.Bigint;
			}
			break;
		}
		case LITERAL_BS_real:
		{
			match(LITERAL_BS_real);
			if ( inputState.guessing==0 ) {
				self = JmlStdType.Real;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CType  jTypeSpec(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		int bounds = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_short:
		case LITERAL_void:
		case IDENT:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		{
			self=mjTypeSpec();
			break;
		}
		case LITERAL_BS_TYPE:
		{
			match(LITERAL_BS_TYPE);
			if ( inputState.guessing==0 ) {
				self = JmlStdType.TYPE;
			}
			{
			_loop23:
			do {
				if ((LA(1)==LBRACK)) {
					match(LBRACK);
					match(RBRACK);
					if ( inputState.guessing==0 ) {
						bounds += 1;
					}
				}
				else {
					break _loop23;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
					    if (bounds > 0) {
				// WMD TODO should we add a universe annotation here?
				// for now \\TYPE arrays are always peer.
				self = new CArrayType( self, bounds, null );
					    }
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CType  mjTypeSpec(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		CUniverse array_univ = null;
		CUniverse elem_univ = null;  // WMD
		
		
		switch ( LA(1)) {
		case IDENT:
		{
			self=jClassTypeSpec(null, null);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_short:
		case LITERAL_void:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		{
			self=jBuiltInTypeSpec(null);
			break;
		}
		default:
			if ((_tokenSet_3.member(LA(1))) && (LA(2)==IDENT)) {
				elem_univ=jUniverseSpec();
				self=jClassTypeSpec(elem_univ, null);
			}
			else if ((_tokenSet_3.member(LA(1))) && (_tokenSet_3.member(LA(2)))) {
				array_univ=jUniverseSpec();
				elem_univ=jUniverseSpec();
				self=jClassTypeSpec(elem_univ, array_univ);
			}
			else if ((_tokenSet_3.member(LA(1))) && (_tokenSet_4.member(LA(2)))) {
				array_univ=jUniverseSpec();
				self=jBuiltInTypeSpec(array_univ);
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CUniverse  jUniversePeerSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		switch ( LA(1)) {
		case LITERAL_peer:
		{
			universe=mjUniversePeerSpec();
			break;
		}
		case LITERAL_U_peer:
		{
			universe=jmlUniversePeerSpec();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CUniverse  mjUniversePeerSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_peer);
		if ( inputState.guessing==0 ) {
			
			// explicit peer reference
			universe = CUniversePeer.getUniverse(); 
			
		}
		return universe;
	}
	
	public final CUniverse  jmlUniversePeerSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_U_peer);
		if ( inputState.guessing==0 ) {
			
			// only do something if the universe keywords are enabled
			if( utility.getCompiler().universeKeywords() ) {
			// explicit peer reference
			universe = CUniversePeer.getUniverse(); 
			}
			
		}
		return universe;
	}
	
	public final CUniverse  jUniverseRepSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		switch ( LA(1)) {
		case LITERAL_rep:
		{
			universe=mjUniverseRepSpec();
			break;
		}
		case LITERAL_U_rep:
		{
			universe=jmlUniverseRepSpec();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CUniverse  mjUniverseRepSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_rep);
		if ( inputState.guessing==0 ) {
			
			// simple rep reference
			universe = CUniverseRep.getUniverse();
			
		}
		return universe;
	}
	
	public final CUniverse  jmlUniverseRepSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_U_rep);
		if ( inputState.guessing==0 ) {
			
			// only do something if the universe checks are enabled
			if( utility.getCompiler().universeKeywords() ) {
			// simple rep reference
			universe = CUniverseRep.getUniverse();
			}
			
		}
		return universe;
	}
	
	public final CUniverse  jUniverseReadonlySpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		switch ( LA(1)) {
		case LITERAL_readonly:
		{
			universe=mjUniverseReadonlySpec();
			break;
		}
		case LITERAL_U_readonly:
		{
			universe=jmlUniverseReadonlySpec();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CUniverse  mjUniverseReadonlySpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_readonly);
		if ( inputState.guessing==0 ) {
			
			universe = CUniverseReadonly.getUniverse();
			
		}
		return universe;
	}
	
	public final CUniverse  jmlUniverseReadonlySpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		match(LITERAL_U_readonly);
		if ( inputState.guessing==0 ) {
			
			// only do something if the universe checks are enabled
			if( utility.getCompiler().universeKeywords() ) {
			universe = CUniverseReadonly.getUniverse();
			}
			
		}
		return universe;
	}
	
	public final JClassDeclarationType  jClassDefinition(
		long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		JClassDeclarationType self = null;
		
		Token  t = null;
		Token  ident = null;
		
		CTypeVariable[] typevariables = CTypeVariable.EMPTY;
		TypeBooleanPair	superClass = null;
		TypeWeaklyList 		interfaces = null;
		CParseClassContext	context = getParseClassContext();
		JavadocComment javadoc = null;
		JavaStyleComment[]	comments = utility.getStatementComment();
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		
		
		t = LT(1);
		match(LITERAL_class);
		ident = LT(1);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LT:
		{
			typevariables=jTypeVariableDeclarationList();
			break;
		}
		case LITERAL_extends:
		case LITERAL_implements:
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    try { javadoc = utility.getJavadocComment( startToken );
				    } catch (Exception e) {
					utility.reportTrouble(
					    new CWarning(
						sourceRef,
						JmlMessages.JAVADOC_FAILURE, e.toString() ));
					javadoc = null;
				    }
				
		}
		superClass=jSuperClassClause();
		interfaces=jImplementsClause();
		jClassBlock(context);
		if ( inputState.guessing==0 ) {
			
				    self = JmlClassDeclaration.makeInstance(
					sourceRef, mods, ident.getText(), typevariables,
					superClass.type, superClass.bool,
					interfaces.types(), interfaces.weaklyFlags(),
					context.getMethods(), context.getInnerClasses(),
					context.getFieldsAndInits(), context.invariants(),
					context.constraints(),
					context.representsDecls(),
					context.axioms(), context.varAssertions(),
					javadoc, comments, isRefinedCUnit );
				    context.release();
				
		}
		return self;
	}
	
	public final CTypeVariable[]  jTypeVariableDeclarationList(
		
	) throws RecognitionException, TokenStreamException {
		CTypeVariable[] self= CTypeVariable.EMPTY;
		
		
		CTypeVariable tv = null;
		ArrayList  vect = new ArrayList();
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LT);
		if ( inputState.guessing==0 ) {
			utility.setUnmatchedTypeLT(unmatchedTypeLT++);
		}
		tv=jTypeVariableDeclaration();
		if ( inputState.guessing==0 ) {
			vect.add(tv);
		}
		{
		_loop478:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				tv=jTypeVariableDeclaration();
				if ( inputState.guessing==0 ) {
					vect.add(tv);
				}
			}
			else {
				break _loop478;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = (CTypeVariable[])vect.toArray(new CTypeVariable[vect.size()]);
			for (int i =0; i< self.length; i++) {
			self[i].setIndex(i);
			}
			
		}
		match(GT);
		if ( inputState.guessing==0 ) {
			utility.setUnmatchedTypeLT(unmatchedTypeLT--);
		}
		if ( inputState.guessing==0 ) {
			
			if (!utility.allowGeneric) {
			utility.reportTrouble(new PositionedError(sourceRef, MjcMessages.UNSUPPORTED_GENERIC_TYPE, null));
			}
			
		}
		return self;
	}
	
	public final TypeBooleanPair  jSuperClassClause(
		
	) throws RecognitionException, TokenStreamException {
		TypeBooleanPair self = null;
		
		
		CClassType type = null;
		boolean _weakly = false;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			match(LITERAL_extends);
			type=jTypeName(null);
			{
			switch ( LA(1)) {
			case LITERAL_weakly:
			{
				match(LITERAL_weakly);
				if ( inputState.guessing==0 ) {
					_weakly = true;
				}
				break;
			}
			case LITERAL_implements:
			case LCURLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_implements:
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			self = new TypeBooleanPair( type, _weakly );
		}
		return self;
	}
	
	public final TypeWeaklyList  jImplementsClause(
		
	) throws RecognitionException, TokenStreamException {
		TypeWeaklyList self = new TypeWeaklyList();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_implements:
		{
			match(LITERAL_implements);
			jNameWeaklyList(self);
			break;
		}
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final void jClassBlock(
		CParseClassContext context
	) throws RecognitionException, TokenStreamException {
		
		Token  f1 = null;
		Token  t = null;
		Token  f2 = null;
		
		
		
		f1 = LT(1);
		match(LCURLY);
		if ( inputState.guessing==0 ) {
			utility.flushJavadocTokensWithWarning( f1 );
		}
		{
		_loop511:
		do {
			switch ( LA(1)) {
			case LITERAL_abstract:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_class:
			case LITERAL_double:
			case LITERAL_final:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_interface:
			case LITERAL_long:
			case LITERAL_native:
			case LITERAL_private:
			case LITERAL_protected:
			case LITERAL_public:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_pure:
			case LITERAL_short:
			case LITERAL_static:
			case LITERAL_strictfp:
			case LITERAL_synchronized:
			case LITERAL_transient:
			case LITERAL_void:
			case LITERAL_volatile:
			case LCURLY:
			case LT:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_also:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_axiom:
			case LITERAL_behavior:
			case LITERAL_behaviour:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_code:
			case LITERAL_code_bigint_math:
			case LITERAL_code_java_math:
			case LITERAL_code_safe_math:
			case LITERAL_constraint:
			case LITERAL_constraint_redundantly:
			case LITERAL_constructor:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exceptional_behavior:
			case LITERAL_exceptional_behaviour:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_extract:
			case LITERAL_field:
			case LITERAL_forall:
			case LITERAL_for_example:
			case LITERAL_ghost:
			case LITERAL_helper:
			case LITERAL_implies_that:
			case LITERAL_initially:
			case LITERAL_instance:
			case LITERAL_invariant:
			case LITERAL_invariant_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_method:
			case LITERAL_model:
			case LITERAL_model_program:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_monitored:
			case LITERAL_monitors_for:
			case LITERAL_non_null:
			case LITERAL_non_null_by_default:
			case LITERAL_normal_behavior:
			case LITERAL_normal_behaviour:
			case LITERAL_nullable:
			case LITERAL_nullable_by_default:
			case LITERAL_old:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_query:
			case LITERAL_readable:
			case LITERAL_represents:
			case LITERAL_represents_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_secret:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_spec_bigint_math:
			case LITERAL_spec_java_math:
			case LITERAL_spec_protected:
			case LITERAL_spec_public:
			case LITERAL_spec_safe_math:
			case LITERAL_uninitialized:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			case LITERAL_writable:
			case LCURLY_VBAR:
			{
				jMember(context);
				break;
			}
			case SEMI:
			{
				t = LT(1);
				match(SEMI);
				if ( inputState.guessing==0 ) {
					
					TokenReference pos = utility.buildTokenReference( t );
					utility.reportTrouble(
					new CWarning( pos, MjcMessages.STRAY_SEMICOLON, null )); 
					
				}
				break;
			}
			default:
			{
				break _loop511;
			}
			}
		} while (true);
		}
		f2 = LT(1);
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			utility.flushJavadocTokensWithWarning( f2 );
		}
	}
	
	public final CClassType  jTypeName(
		CUniverse elem_univ
	) throws RecognitionException, TokenStreamException {
		CClassType self = null;
		
		Token  i = null;
		Token  j = null;
		
		String        name = null;
		CClassType[]  typeParameters = null;
		CClassType[][] allTypeParameters ;
		ArrayList vect = new ArrayList();
		StringBuffer buffer = null;
		
		
		i = LT(1);
		match(IDENT);
		{
		if ((LA(1)==LT)) {
			typeParameters=jParameterizedClassTypeList();
		}
		else if ((_tokenSet_5.member(LA(1)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		if ( inputState.guessing==0 ) {
			
			vect.add(typeParameters);
			typeParameters = null;
			
		}
		{
		_loop469:
		do {
			if ((LA(1)==DOT)) {
				match(DOT);
				j = LT(1);
				match(IDENT);
				{
				if ((LA(1)==LT)) {
					typeParameters=jParameterizedClassTypeList();
				}
				else if ((_tokenSet_5.member(LA(1)))) {
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				if ( inputState.guessing==0 ) {
					
					vect.add(typeParameters);
					typeParameters = null;
					(buffer == null 
					? (buffer = new StringBuffer(i.getText())) : buffer)
					.append('/').append(j.getText()); 
					
				}
			}
			else {
				break _loop469;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			//need to be change later
			name = buffer == null ? i.getText() : buffer.toString();
			allTypeParameters = (CClassType[][])vect.toArray(new CClassType[vect.size()][]);
			self = CTopLevel.getTypeRep(name,elem_univ,allTypeParameters,false);
			
		}
		return self;
	}
	
	public final JInterfaceDeclarationType  jInterfaceDefinition(
		long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		JInterfaceDeclarationType self = null;
		
		Token  t = null;
		Token  ident = null;
		
		CTypeVariable[] typevariables = CTypeVariable.EMPTY;
		TypeWeaklyList		interfaces =  null;
		CParseClassContext context = getParseClassContext();
		JavadocComment javadoc = null;
		JavaStyleComment[]	comments = utility.getStatementComment();
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		
		
		t = LT(1);
		match(LITERAL_interface);
		ident = LT(1);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LT:
		{
			typevariables=jTypeVariableDeclarationList();
			break;
		}
		case LITERAL_extends:
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    try { javadoc = utility.getJavadocComment( startToken );
				    } catch (Exception e) {
					utility.reportTrouble(
					    new CWarning(
						sourceRef,
						JmlMessages.JAVADOC_FAILURE, e.toString() ));
					javadoc = null;
				    }
				
		}
		interfaces=jInterfaceExtends();
		jClassBlock(context);
		if ( inputState.guessing==0 ) {
			
				    self = JmlInterfaceDeclaration.makeInstance(
					sourceRef, mods, ident.getText(), typevariables, interfaces.types(),
					interfaces.weaklyFlags(), context.getMethods(),
					context.getInnerClasses(), context.getFieldsAndInits(),
					context.invariants(),
					context.constraints(),
					context.representsDecls(),
					context.axioms(), context.varAssertions(),
					javadoc, comments, isRefinedCUnit );
				    context.release();
				
		}
		return self;
	}
	
	public final TypeWeaklyList  jInterfaceExtends(
		
	) throws RecognitionException, TokenStreamException {
		TypeWeaklyList self = new TypeWeaklyList();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			match(LITERAL_extends);
			jNameWeaklyList(self);
			break;
		}
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final MJTopLevelMethodDeclaration  mjTopLevelMethodDeclaration(
		long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		MJTopLevelMethodDeclaration self = null;
		
		Token  ident = null;
		
		CType type;					// the method return type
		CType openClass;			// the class that this method extends
		JFormalParameter[]	params;	// an array of the formals
		CClassType[] throwsList = CClassType.EMPTY;	// array of poss. exceptions
		JStatement[] body = null;	// array of the statements in the body
		int bounds = 0;				// does the method return an array
		JavadocComment javadoc = null;
		JavaStyleComment[]	comments = utility.getStatementComment();
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		ParsingController.TokenWrapper declEnd =
		new ParsingController.TokenWrapper();
		JmlMethodSpecification methodSpec = null;
		JmlMethodSpecification internalMethodSpec = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			methodSpec=jmlMethodSpecification(mods);
			if ( inputState.guessing==0 ) {
				startToken = LT(1);
			}
			mods=jModifiers();
			{
			switch ( LA(1)) {
			case LITERAL_method:
			{
				match(LITERAL_method);
				if ( inputState.guessing==0 ) {
					
					utility.flushJavadocTokensWithWarning( declEnd );
					
				}
				break;
			}
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_short:
			case LITERAL_void:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_method:
		{
			match(LITERAL_method);
			if ( inputState.guessing==0 ) {
				
				utility.flushJavadocTokensWithWarning( declEnd );
				
			}
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_short:
		case LITERAL_void:
		case IDENT:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		type=jTypeSpec();
		if ( inputState.guessing==0 ) {
			
				    javadoc = utility.getJavadocComment( startToken );
				
		}
		openClass=mjExternalClassTypeSpec();
		ident = LT(1);
		match(IDENT);
		match(LPAREN);
		params=jParameterDeclarationList(JLocalVariable.DES_PARAMETER);
		match(RPAREN);
		{
		_loop41:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop41;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(new CWarning(sourceRef, 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(new CWarning(sourceRef,
						            MjcMessages.OLD_STYLE_ARRAY_BOUNDS,
			null));
			}
			type = new CArrayType(type, bounds, null);
				    }
				
		}
		{
		switch ( LA(1)) {
		case LITERAL_throws:
		{
			throwsList=jThrowsClause();
			break;
		}
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LCURLY:
		case SEMI:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		{
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			internalMethodSpec=jmlMethodSpecification(mods);
			break;
		}
		case LCURLY:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		}
		if (!( methodSpec == null || internalMethodSpec == null ))
		  throw new SemanticException(" methodSpec == null || internalMethodSpec == null ");
		{
		switch ( LA(1)) {
		case LCURLY:
		{
			body=jCompoundStatement(declEnd);
			break;
		}
		case SEMI:
		{
			match(SEMI);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			/* !FIXME!top-level-method-specs Do the right thing with
			methodSpec */
			
			if (methodSpec != null || internalMethodSpec != null) {
			System.out.println( "Ignoring top level method specification" );
			}
			
				    self = new MJTopLevelMethodDeclaration(
					sourceRef,
					mods,
			CTypeVariable.EMPTY,        
					type,
					openClass,
					ident.getText(),
					params,
					throwsList,
					body == null ? null : new JBlock(sourceRef, body, null),
					javadoc,
					comments );
				    utility.flushJavadocTokensWithWarning( declEnd );
				
		}
		return self;
	}
	
	public final JmlMethodSpecification  jmlMethodSpecification(
		long mods
	) throws RecognitionException, TokenStreamException {
		 JmlMethodSpecification self = null ;
		
		
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			self=jmlSpecification(mods);
			break;
		}
		case LITERAL_also:
		{
			self=jmlExtendingSpecification();
			if ( inputState.guessing==0 ) {
				
					    if (mods != 0 ) {
						utility.reportTrouble( new PositionedError(
							self.getTokenReference(),
							JmlMessages.EXTENDING_SPEC_MODIFIERS ));
					    }
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final long  jModifiers(
		
	) throws RecognitionException, TokenStreamException {
		long self = 0;
		
		
		long        mod; 
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		_loop456:
		do {
			if ((_tokenSet_6.member(LA(1))) && (_tokenSet_7.member(LA(2)))) {
				mod=jModifier();
				if ( inputState.guessing==0 ) {
					
					if ((mod & self) != 0) {
					utility.reportTrouble(
					new PositionedError(sourceRef,
					MjcMessages.DUPLICATE_MODIFIER,
					utility.getModifierName(mod))); 
					}
					
					if (!utility.modifiersInPreferredOrder(self, mod)) { 
					utility.reportTrouble(
					new CWarning(sourceRef,
					MjcMessages.MODIFIER_ORDER,
					utility.getModifierName(mod))); 
					}
					self |= mod;
					
				}
			}
			else {
				break _loop456;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final CType  mjExternalClassTypeSpec(
		
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		Token  i = null;
		Token  j = null;
		
		String        name = null;
		StringBuffer    nameBuf = null;
		CClassType[] typeParameters = null;
		CClassType[][] allTypeParameters ;
		ArrayList vect = new ArrayList();
		
		
		i = LT(1);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LT:
		{
			typeParameters=jParameterizedClassTypeList();
			break;
		}
		case DOT:
		case IDENT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			vect.add(typeParameters);
			typeParameters = null;
			
		}
		{
		_loop491:
		do {
			boolean synPredMatched489 = false;
			if (((LA(1)==DOT) && (LA(2)==DOT||LA(2)==IDENT))) {
				int _m489 = mark();
				synPredMatched489 = true;
				inputState.guessing++;
				try {
					{
					match(DOT);
					match(IDENT);
					match(LPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched489 = false;
				}
				rewind(_m489);
inputState.guessing--;
			}
			if ( synPredMatched489 ) {
				match(DOT);
			}
			else if ((LA(1)==DOT) && (LA(2)==IDENT)) {
				match(DOT);
				j = LT(1);
				match(IDENT);
				{
				switch ( LA(1)) {
				case LT:
				{
					typeParameters=jParameterizedClassTypeList();
					break;
				}
				case DOT:
				case IDENT:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					
					vect.add(typeParameters);
					typeParameters = null;
					(nameBuf == null 
					? (nameBuf = new StringBuffer(i.getText())) : nameBuf)
					.append('/').append(j.getText());
				}
			}
			else {
				break _loop491;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			name = nameBuf == null ? i.getText() : nameBuf.toString();
			allTypeParameters = (CClassType[][])vect.toArray(new CClassType[vect.size()][]);
			self = CTopLevel.getTypeRep(name,allTypeParameters,false);
			
		}
		return self;
	}
	
	public final JFormalParameter[]  jParameterDeclarationList(
		int desc
	) throws RecognitionException, TokenStreamException {
		JFormalParameter[] self = JFormalParameter.EMPTY;
		
		
		JFormalParameter        elem = null;
		ArrayList            vect = new ArrayList();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_final:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_pure:
		case LITERAL_short:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_void:
		case LITERAL_volatile:
		case IDENT:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_extract:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_instance:
		case LITERAL_model:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_query:
		case LITERAL_secret:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		{
			elem=jParameterDeclaration(desc);
			if ( inputState.guessing==0 ) {
				vect.add(elem);
			}
			{
			_loop530:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					elem=jParameterDeclaration(desc);
					if ( inputState.guessing==0 ) {
						vect.add(elem);
					}
				}
				else {
					break _loop530;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				self = new JFormalParameter[vect.size()];
				self = (JFormalParameter[]) vect.toArray(self);
				
				
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final CClassType[]  jThrowsClause(
		
	) throws RecognitionException, TokenStreamException {
		CClassType[] self;
		
		
		match(LITERAL_throws);
		self=jNameList();
		return self;
	}
	
	public final JStatement[]  jCompoundStatement(
		ParsingController.TokenWrapper declEnd
	) throws RecognitionException, TokenStreamException {
		JStatement[] self = null;
		
		Token  s = null;
		Token  e = null;
		
		ArrayList        body = new ArrayList();
		JStatement        stmt;
		
		
		s = LT(1);
		match(LCURLY);
		{
		_loop534:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				stmt=jStatement();
				if ( inputState.guessing==0 ) {
					
					if (stmt instanceof JEmptyStatement) {
					utility.reportTrouble(
					new CWarning(stmt.getTokenReference(), 
					MjcMessages.STRAY_SEMICOLON, null));
					}
					body.add(stmt);
				}
			}
			else {
				break _loop534;
			}
			
		} while (true);
		}
		e = LT(1);
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
			utility.wrapIfEmptyNonNullWrapper( declEnd, e );
			self = new JStatement[body.size()];
			self = (JStatement[]) body.toArray(self);
			
			
		}
		return self;
	}
	
	public final void jNameWeaklyList(
		TypeWeaklyList self
	) throws RecognitionException, TokenStreamException {
		
		
		CClassType type;
		boolean _weakly = false;
		
		
		type=jTypeName(null);
		{
		switch ( LA(1)) {
		case LITERAL_weakly:
		{
			match(LITERAL_weakly);
			if ( inputState.guessing==0 ) {
				_weakly = true;
			}
			break;
		}
		case COMMA:
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    self.add( type, _weakly );
				    _weakly = false;		// reset for next use
				
		}
		{
		_loop54:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				type=jTypeName(null);
				{
				switch ( LA(1)) {
				case LITERAL_weakly:
				{
					match(LITERAL_weakly);
					if ( inputState.guessing==0 ) {
						_weakly = true;
					}
					break;
				}
				case COMMA:
				case LCURLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					
							self.add( type, _weakly );
							_weakly = false;		// reset for next use
						
				}
			}
			else {
				break _loop54;
			}
			
		} while (true);
		}
	}
	
	public final void jMember(
		CParseClassContext context
	) throws RecognitionException, TokenStreamException {
		
		Token  siSpecEnd = null;
		Token  iSpecEnd = null;
		Token  scIdent = null;
		Token  smEnd4 = null;
		Token  smIdent = null;
		Token  smEnd2 = null;
		Token  ctor = null;
		Token  smEnd3 = null;
		Token  ident = null;
		Token  f1 = null;
		Token  f2 = null;
		Token  aStart = null;
		Token  aEnd = null;
		
		CTypeVariable[] typevariables = CTypeVariable.EMPTY;
		JStatement[] body = null;
		JTypeDeclarationType decl;
		CType type;
		JFormalParameter[] params;
		int bounds = 0;
		CClassType[] throwsList = CClassType.EMPTY;
		JVariableDefinition[] vars;
		Token startToken = LT(1);
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		ParsingController.TokenWrapper declEnd =
		new ParsingController.TokenWrapper();
		JavadocComment javadoc = null;
		long mods=0;
		JmlPredicate pred = null;
		JmlMethodSpecification methodSpec = null;
		JmlDataGroupAccumulator dataGroups = new JmlDataGroupAccumulator();
		
		
		mods=jModifiers();
		{
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_also:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_for_example:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_implies_that:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			methodSpec=jmlMethodSpecification(mods);
			if ( inputState.guessing==0 ) {
				
						try {
						    javadoc = utility.getJavadocComment( LT(1) );
						} catch (Exception e) {
						    utility.reportTrouble(
							new CWarning(
							    sourceRef,
							    JmlMessages.JAVADOC_FAILURE, e.toString() ));
						    javadoc = null;
						}
						//if (javadoc != null) System.out.println("JAVADOC " + javadoc.text());
					
			}
			{
			switch ( LA(1)) {
			case LITERAL_static_initializer:
			{
				siSpecEnd = LT(1);
				match(LITERAL_static_initializer);
				if ( inputState.guessing==0 ) {
					
							    context.addBlockInitializer(
								new JmlClassBlock(sourceRef, true, javadoc,
								    methodSpec));
							    utility.flushJavadocTokensWithWarning( siSpecEnd );
							
				}
				break;
			}
			case LITERAL_initializer:
			{
				iSpecEnd = LT(1);
				match(LITERAL_initializer);
				if ( inputState.guessing==0 ) {
					
							    context.addBlockInitializer(
								new JmlClassBlock(sourceRef, false, javadoc,
								    methodSpec));
							    utility.flushJavadocTokensWithWarning( iSpecEnd );
							
				}
				break;
			}
			case LCURLY:
			{
				body=jCompoundStatement(declEnd);
				if ( inputState.guessing==0 ) {
					
							    context.addBlockInitializer(
								new JmlClassBlock(
								    sourceRef, false, body, javadoc, methodSpec
								));
							    utility.flushJavadocTokensWithWarning( siSpecEnd );
							
				}
				break;
			}
			default:
				if ((LA(1)==LITERAL_static) && (LA(2)==LCURLY)) {
					match(LITERAL_static);
					body=jCompoundStatement(declEnd);
					if ( inputState.guessing==0 ) {
						
								    context.addBlockInitializer(
									new JmlClassBlock(
									    sourceRef, true, body, javadoc, methodSpec
									));
								    utility.flushJavadocTokensWithWarning( siSpecEnd );
								
					}
				}
				else if ((_tokenSet_9.member(LA(1))) && (_tokenSet_10.member(LA(2)))) {
					mods=jModifiers();
					{
					switch ( LA(1)) {
					case LITERAL_constructor:
					case LITERAL_method:
					{
						{
						switch ( LA(1)) {
						case LITERAL_method:
						{
							match(LITERAL_method);
							break;
						}
						case LITERAL_constructor:
						{
							match(LITERAL_constructor);
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						if ( inputState.guessing==0 ) {
							utility.flushJavadocTokensWithWarning( declEnd );
						}
						break;
					}
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_double:
					case LITERAL_float:
					case LITERAL_int:
					case LITERAL_long:
					case LITERAL_peer:
					case LITERAL_readonly:
					case LITERAL_rep:
					case LITERAL_short:
					case LITERAL_void:
					case LT:
					case IDENT:
					case LITERAL_BS_TYPE:
					case LITERAL_BS_bigint:
					case LITERAL_BS_real:
					case LITERAL_U_peer:
					case LITERAL_U_rep:
					case LITERAL_U_readonly:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					{
					if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
						scIdent = LT(1);
						match(IDENT);
						match(LPAREN);
						params=jParameterDeclarationList(JLocalVariable.DES_PARAMETER);
						match(RPAREN);
						{
						switch ( LA(1)) {
						case LITERAL_throws:
						{
							throwsList=jThrowsClause();
							break;
						}
						case LCURLY:
						case SEMI:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						{
						switch ( LA(1)) {
						case LCURLY:
						{
							body=jCompoundStatement(declEnd);
							if ( inputState.guessing==0 ) {
								
											    utility.flushJavadocTokensWithWarning( declEnd );
											
							}
							break;
						}
						case SEMI:
						{
							smEnd4 = LT(1);
							match(SEMI);
							if ( inputState.guessing==0 ) {
								
											    body = null;
											    utility.flushJavadocTokensWithWarning( smEnd4 );
											
							}
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						if ( inputState.guessing==0 ) {
							
										context.addMethodDeclaration(
										    JmlConstructorDeclaration.makeInstance(
											sourceRef, mods, scIdent.getText(), params,
											throwsList,
											new JConstructorBlockWrapper(sourceRef, body),
											javadoc, utility.getStatementComment(),
											methodSpec
										    ));
									
						}
					}
					else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
						{
						switch ( LA(1)) {
						case LT:
						{
							typevariables=jTypeVariableDeclarationList();
							break;
						}
						case LITERAL_boolean:
						case LITERAL_byte:
						case LITERAL_char:
						case LITERAL_double:
						case LITERAL_float:
						case LITERAL_int:
						case LITERAL_long:
						case LITERAL_peer:
						case LITERAL_readonly:
						case LITERAL_rep:
						case LITERAL_short:
						case LITERAL_void:
						case IDENT:
						case LITERAL_BS_TYPE:
						case LITERAL_BS_bigint:
						case LITERAL_BS_real:
						case LITERAL_U_peer:
						case LITERAL_U_rep:
						case LITERAL_U_readonly:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						type=jTypeSpec();
						smIdent = LT(1);
						match(IDENT);
						match(LPAREN);
						params=jParameterDeclarationList(JLocalVariable.DES_PARAMETER);
						match(RPAREN);
						{
						_loop65:
						do {
							if ((LA(1)==LBRACK)) {
								match(LBRACK);
								match(RBRACK);
								if ( inputState.guessing==0 ) {
									bounds += 1;
								}
							}
							else {
								break _loop65;
							}
							
						} while (true);
						}
						if ( inputState.guessing==0 ) {
							
										    if (bounds > 0) {
							if( utility.getCompiler().universeChecks() ) {
							utility.reportTrouble(new CWarning(sourceRef, 
							CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
							null));
							} else {
							utility.reportTrouble(new CWarning(sourceRef,
							MjcMessages.OLD_STYLE_ARRAY_BOUNDS,
							null));
							}
										        type = new CArrayType(type, bounds, null);
										    }
									
						}
						{
						switch ( LA(1)) {
						case LITERAL_throws:
						{
							throwsList=jThrowsClause();
							break;
						}
						case LCURLY:
						case SEMI:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						{
						switch ( LA(1)) {
						case LCURLY:
						{
							body=jCompoundStatement(declEnd);
							if ( inputState.guessing==0 ) {
								
											    utility.flushJavadocTokensWithWarning( declEnd );
											
							}
							break;
						}
						case SEMI:
						{
							smEnd2 = LT(1);
							match(SEMI);
							if ( inputState.guessing==0 ) {
								
											    body = null;
											    utility.flushJavadocTokensWithWarning( smEnd2 );
											
							}
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						if ( inputState.guessing==0 ) {
							
										context.addMethodDeclaration(
										    JmlMethodDeclaration.makeInstance(
											sourceRef, mods, typevariables, type, smIdent.getText(),
											params, throwsList,
											body == null ? null :
											new JBlock(sourceRef, body, null),
											javadoc, utility.getStatementComment(),
											methodSpec
										    ));
									
						}
					}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					
					}
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_short:
		case LITERAL_void:
		case LT:
		case IDENT:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case LITERAL_constructor:
		case LITERAL_field:
		case LITERAL_method:
		{
			{
			{
			switch ( LA(1)) {
			case LITERAL_constructor:
			case LITERAL_field:
			case LITERAL_method:
			{
				{
				switch ( LA(1)) {
				case LITERAL_constructor:
				{
					match(LITERAL_constructor);
					break;
				}
				case LITERAL_method:
				{
					match(LITERAL_method);
					break;
				}
				case LITERAL_field:
				{
					match(LITERAL_field);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					utility.flushJavadocTokensWithWarning( declEnd );
				}
				break;
			}
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_short:
			case LITERAL_void:
			case LT:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
				ctor = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					
							try { javadoc = utility.getJavadocComment( startToken );
							} catch (Exception e) {
							    utility.reportTrouble(
								new CWarning(
								    sourceRef,
								    JmlMessages.JAVADOC_FAILURE, e.toString() ));
							    javadoc = null;
							}
						
				}
				match(LPAREN);
				params=jParameterDeclarationList(
		JLocalVariable.DES_PARAMETER);
				match(RPAREN);
				{
				switch ( LA(1)) {
				case LITERAL_throws:
				{
					throwsList=jThrowsClause();
					break;
				}
				case LITERAL_abstract:
				case LITERAL_final:
				case LITERAL_native:
				case LITERAL_private:
				case LITERAL_protected:
				case LITERAL_public:
				case LITERAL_pure:
				case LITERAL_static:
				case LITERAL_strictfp:
				case LITERAL_synchronized:
				case LITERAL_transient:
				case LITERAL_volatile:
				case LCURLY:
				case SEMI:
				case LITERAL_accessible:
				case LITERAL_accessible_redundantly:
				case LITERAL_also:
				case LITERAL_assignable:
				case LITERAL_assignable_redundantly:
				case LITERAL_behavior:
				case LITERAL_behaviour:
				case LITERAL_breaks:
				case LITERAL_breaks_redundantly:
				case LITERAL_callable:
				case LITERAL_callable_redundantly:
				case LITERAL_captures:
				case LITERAL_captures_redundantly:
				case LITERAL_code:
				case LITERAL_code_bigint_math:
				case LITERAL_code_java_math:
				case LITERAL_code_safe_math:
				case LITERAL_continues:
				case LITERAL_continues_redundantly:
				case LITERAL_diverges:
				case LITERAL_diverges_redundantly:
				case LITERAL_duration:
				case LITERAL_duration_redundantly:
				case LITERAL_ensures:
				case LITERAL_ensures_redundantly:
				case LITERAL_exceptional_behavior:
				case LITERAL_exceptional_behaviour:
				case LITERAL_exsures:
				case LITERAL_exsures_redundantly:
				case LITERAL_extract:
				case LITERAL_forall:
				case LITERAL_for_example:
				case LITERAL_ghost:
				case LITERAL_helper:
				case LITERAL_implies_that:
				case LITERAL_instance:
				case LITERAL_measured_by:
				case LITERAL_measured_by_redundantly:
				case LITERAL_model:
				case LITERAL_model_program:
				case LITERAL_modifiable:
				case LITERAL_modifiable_redundantly:
				case LITERAL_modifies:
				case LITERAL_modifies_redundantly:
				case LITERAL_monitored:
				case LITERAL_non_null:
				case LITERAL_non_null_by_default:
				case LITERAL_normal_behavior:
				case LITERAL_normal_behaviour:
				case LITERAL_nullable:
				case LITERAL_nullable_by_default:
				case LITERAL_old:
				case LITERAL_post:
				case LITERAL_post_redundantly:
				case LITERAL_pre:
				case LITERAL_pre_redundantly:
				case LITERAL_query:
				case LITERAL_requires:
				case LITERAL_requires_redundantly:
				case LITERAL_returns:
				case LITERAL_returns_redundantly:
				case LITERAL_secret:
				case LITERAL_signals:
				case LITERAL_signals_only:
				case LITERAL_signals_only_redundantly:
				case LITERAL_signals_redundantly:
				case LITERAL_spec_bigint_math:
				case LITERAL_spec_java_math:
				case LITERAL_spec_protected:
				case LITERAL_spec_public:
				case LITERAL_spec_safe_math:
				case LITERAL_uninitialized:
				case LITERAL_when:
				case LITERAL_when_redundantly:
				case LITERAL_working_space:
				case LITERAL_working_space_redundantly:
				case LCURLY_VBAR:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				{
				switch ( LA(1)) {
				case LITERAL_abstract:
				case LITERAL_final:
				case LITERAL_native:
				case LITERAL_private:
				case LITERAL_protected:
				case LITERAL_public:
				case LITERAL_pure:
				case LITERAL_static:
				case LITERAL_strictfp:
				case LITERAL_synchronized:
				case LITERAL_transient:
				case LITERAL_volatile:
				case LITERAL_accessible:
				case LITERAL_accessible_redundantly:
				case LITERAL_also:
				case LITERAL_assignable:
				case LITERAL_assignable_redundantly:
				case LITERAL_behavior:
				case LITERAL_behaviour:
				case LITERAL_breaks:
				case LITERAL_breaks_redundantly:
				case LITERAL_callable:
				case LITERAL_callable_redundantly:
				case LITERAL_captures:
				case LITERAL_captures_redundantly:
				case LITERAL_code:
				case LITERAL_code_bigint_math:
				case LITERAL_code_java_math:
				case LITERAL_code_safe_math:
				case LITERAL_continues:
				case LITERAL_continues_redundantly:
				case LITERAL_diverges:
				case LITERAL_diverges_redundantly:
				case LITERAL_duration:
				case LITERAL_duration_redundantly:
				case LITERAL_ensures:
				case LITERAL_ensures_redundantly:
				case LITERAL_exceptional_behavior:
				case LITERAL_exceptional_behaviour:
				case LITERAL_exsures:
				case LITERAL_exsures_redundantly:
				case LITERAL_extract:
				case LITERAL_forall:
				case LITERAL_for_example:
				case LITERAL_ghost:
				case LITERAL_helper:
				case LITERAL_implies_that:
				case LITERAL_instance:
				case LITERAL_measured_by:
				case LITERAL_measured_by_redundantly:
				case LITERAL_model:
				case LITERAL_model_program:
				case LITERAL_modifiable:
				case LITERAL_modifiable_redundantly:
				case LITERAL_modifies:
				case LITERAL_modifies_redundantly:
				case LITERAL_monitored:
				case LITERAL_non_null:
				case LITERAL_non_null_by_default:
				case LITERAL_normal_behavior:
				case LITERAL_normal_behaviour:
				case LITERAL_nullable:
				case LITERAL_nullable_by_default:
				case LITERAL_old:
				case LITERAL_post:
				case LITERAL_post_redundantly:
				case LITERAL_pre:
				case LITERAL_pre_redundantly:
				case LITERAL_query:
				case LITERAL_requires:
				case LITERAL_requires_redundantly:
				case LITERAL_returns:
				case LITERAL_returns_redundantly:
				case LITERAL_secret:
				case LITERAL_signals:
				case LITERAL_signals_only:
				case LITERAL_signals_only_redundantly:
				case LITERAL_signals_redundantly:
				case LITERAL_spec_bigint_math:
				case LITERAL_spec_java_math:
				case LITERAL_spec_protected:
				case LITERAL_spec_public:
				case LITERAL_spec_safe_math:
				case LITERAL_uninitialized:
				case LITERAL_when:
				case LITERAL_when_redundantly:
				case LITERAL_working_space:
				case LITERAL_working_space_redundantly:
				case LCURLY_VBAR:
				{
					methodSpec=jmlMethodSpecification(0);
					break;
				}
				case LCURLY:
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				{
				switch ( LA(1)) {
				case LCURLY:
				{
					body=jCompoundStatement(declEnd);
					if ( inputState.guessing==0 ) {
						
								    utility.flushJavadocTokensWithWarning( declEnd );
								
					}
					break;
				}
				case SEMI:
				{
					smEnd3 = LT(1);
					match(SEMI);
					if ( inputState.guessing==0 ) {
						
								    body = null;
								    utility.flushJavadocTokensWithWarning( smEnd3 );
								
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					
							context.addMethodDeclaration(
							    JmlConstructorDeclaration.makeInstance(
								sourceRef, mods, ctor.getText(), params,
								throwsList, new JConstructorBlockWrapper(sourceRef, body),
								javadoc, utility.getStatementComment(), methodSpec
							    ));
						
				}
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case LT:
				{
					typevariables=jTypeVariableDeclarationList();
					break;
				}
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_double:
				case LITERAL_float:
				case LITERAL_int:
				case LITERAL_long:
				case LITERAL_peer:
				case LITERAL_readonly:
				case LITERAL_rep:
				case LITERAL_short:
				case LITERAL_void:
				case IDENT:
				case LITERAL_BS_TYPE:
				case LITERAL_BS_bigint:
				case LITERAL_BS_real:
				case LITERAL_U_peer:
				case LITERAL_U_rep:
				case LITERAL_U_readonly:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				type=jTypeSpec();
				if ( inputState.guessing==0 ) {
					
							try { javadoc = utility.getJavadocComment( startToken );
							} catch (Exception e) {
							    utility.reportTrouble(
								new CWarning(
								    sourceRef,
								    JmlMessages.JAVADOC_FAILURE, e.toString() ));
							    javadoc = null;
							}
						
				}
				{
				if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
					ident = LT(1);
					match(IDENT);
					match(LPAREN);
					params=jParameterDeclarationList(
		    JLocalVariable.DES_PARAMETER);
					match(RPAREN);
					{
					_loop78:
					do {
						if ((LA(1)==LBRACK)) {
							match(LBRACK);
							match(RBRACK);
							if ( inputState.guessing==0 ) {
								bounds += 1;
							}
						}
						else {
							break _loop78;
						}
						
					} while (true);
					}
					if ( inputState.guessing==0 ) {
						
								    if (bounds > 0) {
						if( utility.getCompiler().universeChecks() ) {
						utility.reportTrouble(new CWarning(sourceRef, 
						CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
						null));
						} else {
						utility.reportTrouble(new CWarning(sourceRef,
						MjcMessages.OLD_STYLE_ARRAY_BOUNDS,
						null));
						}
						type = new CArrayType(type, bounds, null);
								    }
								
					}
					{
					switch ( LA(1)) {
					case LITERAL_throws:
					{
						throwsList=jThrowsClause();
						break;
					}
					case LITERAL_abstract:
					case LITERAL_final:
					case LITERAL_native:
					case LITERAL_private:
					case LITERAL_protected:
					case LITERAL_public:
					case LITERAL_pure:
					case LITERAL_static:
					case LITERAL_strictfp:
					case LITERAL_synchronized:
					case LITERAL_transient:
					case LITERAL_volatile:
					case LCURLY:
					case SEMI:
					case LITERAL_accessible:
					case LITERAL_accessible_redundantly:
					case LITERAL_also:
					case LITERAL_assignable:
					case LITERAL_assignable_redundantly:
					case LITERAL_behavior:
					case LITERAL_behaviour:
					case LITERAL_breaks:
					case LITERAL_breaks_redundantly:
					case LITERAL_callable:
					case LITERAL_callable_redundantly:
					case LITERAL_captures:
					case LITERAL_captures_redundantly:
					case LITERAL_code:
					case LITERAL_code_bigint_math:
					case LITERAL_code_java_math:
					case LITERAL_code_safe_math:
					case LITERAL_continues:
					case LITERAL_continues_redundantly:
					case LITERAL_diverges:
					case LITERAL_diverges_redundantly:
					case LITERAL_duration:
					case LITERAL_duration_redundantly:
					case LITERAL_ensures:
					case LITERAL_ensures_redundantly:
					case LITERAL_exceptional_behavior:
					case LITERAL_exceptional_behaviour:
					case LITERAL_exsures:
					case LITERAL_exsures_redundantly:
					case LITERAL_extract:
					case LITERAL_forall:
					case LITERAL_for_example:
					case LITERAL_ghost:
					case LITERAL_helper:
					case LITERAL_implies_that:
					case LITERAL_instance:
					case LITERAL_measured_by:
					case LITERAL_measured_by_redundantly:
					case LITERAL_model:
					case LITERAL_model_program:
					case LITERAL_modifiable:
					case LITERAL_modifiable_redundantly:
					case LITERAL_modifies:
					case LITERAL_modifies_redundantly:
					case LITERAL_monitored:
					case LITERAL_non_null:
					case LITERAL_non_null_by_default:
					case LITERAL_normal_behavior:
					case LITERAL_normal_behaviour:
					case LITERAL_nullable:
					case LITERAL_nullable_by_default:
					case LITERAL_old:
					case LITERAL_post:
					case LITERAL_post_redundantly:
					case LITERAL_pre:
					case LITERAL_pre_redundantly:
					case LITERAL_query:
					case LITERAL_requires:
					case LITERAL_requires_redundantly:
					case LITERAL_returns:
					case LITERAL_returns_redundantly:
					case LITERAL_secret:
					case LITERAL_signals:
					case LITERAL_signals_only:
					case LITERAL_signals_only_redundantly:
					case LITERAL_signals_redundantly:
					case LITERAL_spec_bigint_math:
					case LITERAL_spec_java_math:
					case LITERAL_spec_protected:
					case LITERAL_spec_public:
					case LITERAL_spec_safe_math:
					case LITERAL_uninitialized:
					case LITERAL_when:
					case LITERAL_when_redundantly:
					case LITERAL_working_space:
					case LITERAL_working_space_redundantly:
					case LCURLY_VBAR:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					{
					switch ( LA(1)) {
					case LITERAL_abstract:
					case LITERAL_final:
					case LITERAL_native:
					case LITERAL_private:
					case LITERAL_protected:
					case LITERAL_public:
					case LITERAL_pure:
					case LITERAL_static:
					case LITERAL_strictfp:
					case LITERAL_synchronized:
					case LITERAL_transient:
					case LITERAL_volatile:
					case LITERAL_accessible:
					case LITERAL_accessible_redundantly:
					case LITERAL_also:
					case LITERAL_assignable:
					case LITERAL_assignable_redundantly:
					case LITERAL_behavior:
					case LITERAL_behaviour:
					case LITERAL_breaks:
					case LITERAL_breaks_redundantly:
					case LITERAL_callable:
					case LITERAL_callable_redundantly:
					case LITERAL_captures:
					case LITERAL_captures_redundantly:
					case LITERAL_code:
					case LITERAL_code_bigint_math:
					case LITERAL_code_java_math:
					case LITERAL_code_safe_math:
					case LITERAL_continues:
					case LITERAL_continues_redundantly:
					case LITERAL_diverges:
					case LITERAL_diverges_redundantly:
					case LITERAL_duration:
					case LITERAL_duration_redundantly:
					case LITERAL_ensures:
					case LITERAL_ensures_redundantly:
					case LITERAL_exceptional_behavior:
					case LITERAL_exceptional_behaviour:
					case LITERAL_exsures:
					case LITERAL_exsures_redundantly:
					case LITERAL_extract:
					case LITERAL_forall:
					case LITERAL_for_example:
					case LITERAL_ghost:
					case LITERAL_helper:
					case LITERAL_implies_that:
					case LITERAL_instance:
					case LITERAL_measured_by:
					case LITERAL_measured_by_redundantly:
					case LITERAL_model:
					case LITERAL_model_program:
					case LITERAL_modifiable:
					case LITERAL_modifiable_redundantly:
					case LITERAL_modifies:
					case LITERAL_modifies_redundantly:
					case LITERAL_monitored:
					case LITERAL_non_null:
					case LITERAL_non_null_by_default:
					case LITERAL_normal_behavior:
					case LITERAL_normal_behaviour:
					case LITERAL_nullable:
					case LITERAL_nullable_by_default:
					case LITERAL_old:
					case LITERAL_post:
					case LITERAL_post_redundantly:
					case LITERAL_pre:
					case LITERAL_pre_redundantly:
					case LITERAL_query:
					case LITERAL_requires:
					case LITERAL_requires_redundantly:
					case LITERAL_returns:
					case LITERAL_returns_redundantly:
					case LITERAL_secret:
					case LITERAL_signals:
					case LITERAL_signals_only:
					case LITERAL_signals_only_redundantly:
					case LITERAL_signals_redundantly:
					case LITERAL_spec_bigint_math:
					case LITERAL_spec_java_math:
					case LITERAL_spec_protected:
					case LITERAL_spec_public:
					case LITERAL_spec_safe_math:
					case LITERAL_uninitialized:
					case LITERAL_when:
					case LITERAL_when_redundantly:
					case LITERAL_working_space:
					case LITERAL_working_space_redundantly:
					case LCURLY_VBAR:
					{
						methodSpec=jmlMethodSpecification(0);
						break;
					}
					case LCURLY:
					case SEMI:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					{
					switch ( LA(1)) {
					case LCURLY:
					{
						body=jCompoundStatement(declEnd);
						if ( inputState.guessing==0 ) {
							
										utility.flushJavadocTokensWithWarning( declEnd );
									
						}
						break;
					}
					case SEMI:
					{
						f1 = LT(1);
						match(SEMI);
						if ( inputState.guessing==0 ) {
							
										body = null;
										utility.flushJavadocTokensWithWarning( f1 );
									
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					if ( inputState.guessing==0 ) {
						
								    context.addMethodDeclaration(
									JmlMethodDeclaration.makeInstance(
									    sourceRef, mods, typevariables, type, ident.getText(), params,
									    throwsList,
									    body == null ? null :
									    new JBlock(sourceRef, body, null),
									    javadoc, utility.getStatementComment(),
									    methodSpec
									));
								
					}
				}
				else if ((LA(1)==IDENT) && (_tokenSet_13.member(LA(2)))) {
					vars=jVariableDefinitions(mods, type);
					f2 = LT(1);
					match(SEMI);
					{
					_loop83:
					do {
						if ((_tokenSet_14.member(LA(1)))) {
							jmlDataGroupClause(dataGroups);
						}
						else {
							break _loop83;
						}
						
					} while (true);
					}
					if ( inputState.guessing==0 ) {
						
								    utility.flushJavadocTokensWithWarning( f2 );
								    JavaStyleComment[] comment =
								    utility.getStatementComment();
								    for (int i = 0; i < vars.length; i++) {
									    context.addFieldDeclaration(
									        JmlFieldDeclaration.makeInstance(
										    vars[i].getTokenReference(), vars[i],
										    javadoc, comment, new JmlVarAssertion[0], dataGroups
									        ));
								    }
						if (dataGroups != null) {
						if (vars.length > 1) {
						utility.reportTrouble(
						new CWarning( sourceRef,
						JmlMessages.ASSERTIONS_FOR_MORE_THAN_ONE_VAR,
						null));
						}
						ArrayList mapsIntoList = dataGroups.mapsIntoClauses();
						for ( int i=0; i<mapsIntoList.size(); i++ ) {
						JmlMapsIntoClause nextClause
						= (JmlMapsIntoClause) mapsIntoList.get(i);
						utility.reportTrouble(
						new CWarning( nextClause.getTokenReference(), 
						JmlMessages.INVALID_FIELD_NAME_IN_MAPS_CLAUSE, 
						nextClause.fieldIdent()));
						}
						}
								
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			}
			break;
		}
		case LITERAL_class:
		{
			decl=jClassDefinition(mods,startToken);
			if ( inputState.guessing==0 ) {
				context.addInnerDeclaration(decl);
			}
			break;
		}
		case LITERAL_interface:
		{
			decl=jInterfaceDefinition(mods,startToken);
			if ( inputState.guessing==0 ) {
				context.addInnerDeclaration(decl);
			}
			break;
		}
		case LITERAL_constraint:
		case LITERAL_constraint_redundantly:
		case LITERAL_initially:
		case LITERAL_invariant:
		case LITERAL_invariant_redundantly:
		case LITERAL_monitors_for:
		case LITERAL_readable:
		case LITERAL_represents:
		case LITERAL_represents_redundantly:
		case LITERAL_writable:
		{
			jmlDeclaration(context,mods,startToken);
			break;
		}
		case LCURLY:
		{
			body=jCompoundStatement(declEnd);
			if ( inputState.guessing==0 ) {
				
						if (Utils.hasOtherFlags(mods, Constants.ACC_STATIC)) {
						    utility.reportTrouble( new PositionedError( sourceRef,
							    JmlMessages.BAD_INITIALIZER_MODIFIERS ));
						}
						context.addBlockInitializer(
						    new JmlClassBlock(
							sourceRef,
							Utils.hasFlag(mods, Constants.ACC_STATIC),
							body, utility.getJavadocComment( startToken ), null
						    ));
						utility.flushJavadocTokensWithWarning( declEnd );
					
			}
			break;
		}
		case LITERAL_axiom:
		{
			aStart = LT(1);
			match(LITERAL_axiom);
			pred=jmlPredicate();
			aEnd = LT(1);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
						if (mods!=0) {
						    utility.reportTrouble( new PositionedError( sourceRef,
							    JmlMessages.AXIOM_MODIFIERS ));
						}
						context.addAxiom(
						    new JmlAxiom( sourceRef, pred ));
						utility.flushJavadocTokensWithWarning( aEnd );
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
	}
	
	public final JVariableDefinition[]  jVariableDefinitions(
		long mods, CType type
	) throws RecognitionException, TokenStreamException {
		JVariableDefinition[] self = null;
		
		
		ArrayList        vars = new ArrayList();
		JVariableDefinition    decl;
		
		
		decl=jVariableDeclarator(mods, type);
		if ( inputState.guessing==0 ) {
			vars.add(decl);
		}
		{
		_loop514:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				decl=jVariableDeclarator(mods, type);
				if ( inputState.guessing==0 ) {
					vars.add(decl);
				}
			}
			else {
				break _loop514;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new JVariableDefinition[vars.size()];
			self = (JVariableDefinition[]) vars.toArray(self);
			
			
		}
		return self;
	}
	
	public final void jmlDataGroupClause(
		JmlDataGroupAccumulator self
	) throws RecognitionException, TokenStreamException {
		
		
		boolean redundant = false;
		JmlStoreRefExpression[] groupList = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		String fieldId = null;
		JmlStoreRefExpression memberRef = null;
		
		
		switch ( LA(1)) {
		case LITERAL_in:
		case LITERAL_in_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_in:
			{
				match(LITERAL_in);
				break;
			}
			case LITERAL_in_redundantly:
			{
				match(LITERAL_in_redundantly);
				if ( inputState.guessing==0 ) {
					redundant = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			groupList=jmlGroupList();
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
					    self.addInGroup( new JmlInGroupClause( sourceRef, redundant,
				groupList ) );
					
			}
			break;
		}
		case LITERAL_maps:
		case LITERAL_maps_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_maps:
			{
				match(LITERAL_maps);
				break;
			}
			case LITERAL_maps_redundantly:
			{
				match(LITERAL_maps_redundantly);
				if ( inputState.guessing==0 ) {
					redundant = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			memberRef=jmlMapsReference();
			if ( inputState.guessing==0 ) {
				
				fieldId = memberRef.names()[0].ident();
					
			}
			match(LITERAL_BS_into);
			groupList=jmlGroupList();
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
					    self.addMapsInto( new JmlMapsIntoClause( sourceRef, redundant,
				fieldId,
				memberRef,
				groupList ) );
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void jmlDeclaration(
		CParseClassContext context,long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		
		Token  rId = null;
		Token  wId = null;
		Token  mId = null;
		Token  e = null;
		
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		JmlInvariant inv = null;
		JmlPredicate pred = null;
		boolean redundant = false;
		JmlMethodNameList mnList = null;
		JmlStoreRefExpression storeRef = null;
		JmlStoreRef[] storeRefList = null;
		JmlSpecExpression specExpr = null;
		JmlSpecExpression[] specs = null;
			JNameExpression fieldName = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_invariant:
		case LITERAL_invariant_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_invariant:
			{
				match(LITERAL_invariant);
				break;
			}
			case LITERAL_invariant_redundantly:
			{
				match(LITERAL_invariant_redundantly);
				if ( inputState.guessing==0 ) {
					redundant = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			pred=jmlPredicate();
			if ( inputState.guessing==0 ) {
				
						context.addInvariant(
						    new JmlInvariant( sourceRef, mods, redundant, pred ));
					
			}
			break;
		}
		case LITERAL_constraint:
		case LITERAL_constraint_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_constraint:
			{
				match(LITERAL_constraint);
				break;
			}
			case LITERAL_constraint_redundantly:
			{
				match(LITERAL_constraint_redundantly);
				if ( inputState.guessing==0 ) {
					redundant = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			pred=jmlPredicate();
			{
			switch ( LA(1)) {
			case LITERAL_for:
			{
				match(LITERAL_for);
				{
				switch ( LA(1)) {
				case LITERAL_BS_everything:
				{
					match(LITERAL_BS_everything);
					break;
				}
				case LITERAL_new:
				case LITERAL_super:
				case LITERAL_this:
				case IDENT:
				{
					mnList=jmlMethodNameList();
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
						context.addConstraint(
				new JmlConstraint( sourceRef, mods, redundant, pred,
				mnList ));
					
			}
			break;
		}
		case LITERAL_represents:
		case LITERAL_represents_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_represents:
			{
				match(LITERAL_represents);
				break;
			}
			case LITERAL_represents_redundantly:
			{
				match(LITERAL_represents_redundantly);
				if ( inputState.guessing==0 ) {
					redundant = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			storeRef=jmlStoreRefExpression();
			{
			switch ( LA(1)) {
			case ASSIGN:
			case L_ARROW:
			{
				{
				switch ( LA(1)) {
				case ASSIGN:
				{
					match(ASSIGN);
					break;
				}
				case L_ARROW:
				{
					match(L_ARROW);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				specExpr=jmlSpecExpression();
				if ( inputState.guessing==0 ) {
					
							    context.addRepresentsDecl(
								new JmlRepresentsDecl( sourceRef, mods, redundant,
								    storeRef, specExpr ));
					
							
				}
				break;
			}
			case LITERAL_BS_such_that:
			{
				match(LITERAL_BS_such_that);
				pred=jmlPredicate();
				if ( inputState.guessing==0 ) {
					
							    context.addRepresentsDecl(
								new JmlRepresentsDecl( sourceRef, mods, redundant,
								    storeRef, pred ));
					
							
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_initially:
		{
			match(LITERAL_initially);
			pred=jmlPredicate();
			if ( inputState.guessing==0 ) {
				
						    context.addVarAssertion(
					            new JmlInitiallyVarAssertion( sourceRef, mods, pred ) );
					
			}
			break;
		}
		case LITERAL_readable:
		{
			match(LITERAL_readable);
			rId = LT(1);
			match(IDENT);
			match(LITERAL_if);
			if ( inputState.guessing==0 ) {
				
				fieldName = new JNameExpression(utility.buildTokenReference(rId),
				rId.getText());
					
			}
			pred=jmlPredicate();
			if ( inputState.guessing==0 ) {
				
						    context.addVarAssertion(
					            new JmlReadableIfVarAssertion( sourceRef, mods,
				fieldName, pred ) );
					
			}
			break;
		}
		case LITERAL_writable:
		{
			match(LITERAL_writable);
			wId = LT(1);
			match(IDENT);
			match(LITERAL_if);
			if ( inputState.guessing==0 ) {
				
				fieldName = new JNameExpression(utility.buildTokenReference(wId),
				wId.getText());
					
			}
			pred=jmlPredicate();
			if ( inputState.guessing==0 ) {
				
						    context.addVarAssertion(
					            new JmlWritableIfVarAssertion( sourceRef, mods,
				fieldName, pred ) );
					
			}
			break;
		}
		case LITERAL_monitors_for:
		{
			match(LITERAL_monitors_for);
			mId = LT(1);
			match(IDENT);
			{
			switch ( LA(1)) {
			case ASSIGN:
			{
				match(ASSIGN);
				break;
			}
			case L_ARROW:
			{
				match(L_ARROW);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				fieldName = new JNameExpression(utility.buildTokenReference(mId),
				mId.getText());
					
			}
			specs=jmlSpecExpressionList();
			if ( inputState.guessing==0 ) {
				
						    context.addVarAssertion(
					            new JmlMonitorsForVarAssertion( sourceRef, mods,
				fieldName, specs ) );
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		e = LT(1);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			utility.flushJavadocTokensWithWarning( e );
		}
	}
	
	public final JmlPredicate  jmlPredicate(
		
	) throws RecognitionException, TokenStreamException {
		JmlPredicate self=null;
		
		
		JmlSpecExpression expr = null;
		
		
		expr=jmlSpecExpression();
		if ( inputState.guessing==0 ) {
			
				    self = new JmlPredicate( expr );
				
		}
		return self;
	}
	
	public final JFormalParameter  jParameterDeclaration(
		int desc
	) throws RecognitionException, TokenStreamException {
		JFormalParameter self = null;
		
		Token  ident = null;
		
		long	mods = 0;
		boolean	finalWasFirst = false;
		int		bounds = 0;
		CType	type;
		CType	ddType = null;		// type of (optional) dynamic dispatch annot.
		TokenReference	sourceRef = utility.buildTokenReference();
		
		
		mods=jModifiers();
		type=jTypeSpec();
		{
		if (((LA(1)==AT))&&(utility.allowMultiJava)) {
			{
			if ((LA(1)==AT) && (_tokenSet_15.member(LA(2)))) {
				match(AT);
				ddType=jTypeSpec();
			}
			else if ((LA(1)==AT) && (LA(2)==AT)) {
				match(AT);
				match(AT);
				ddType=jValueSpecializer(type, sourceRef);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		else if ((LA(1)==IDENT)) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		ident = LT(1);
		match(IDENT);
		{
		_loop88:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop88;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(new CWarning(sourceRef, 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(new CWarning(sourceRef,
						    MjcMessages.OLD_STYLE_ARRAY_BOUNDS));
			}
					type = new CArrayType(type, bounds, null);
				}
				    CSpecializedType specializedType;
				    if (ddType == null) {
					    specializedType = new CSpecializedType( type );
				    } else {
					    specializedType = new CSpecializedType( type, ddType );
				    }
				    self = new JmlFormalParameter( sourceRef, mods, desc, specializedType, ident.getText());
				
		}
		return self;
	}
	
	public final CType  jValueSpecializer(
		CType type, TokenReference sourceRef
	) throws RecognitionException, TokenStreamException {
		CType specType = null;
		
		
		JExpression expr;
		
		
		expr=jExpression();
		if ( inputState.guessing==0 ) {
			if (type.isOrdinal())
			specType = new COrdinalValueType(type, expr);
			else if (type.isFloatingPoint())
			specType = new CRealValueType(type, expr);
			else if (type.isBoolean())
			specType = new CBooleanValueType(expr);
			else
			// we can't check here whether the static type is java.lang.String,
			// so we'll assume it is and check later
			specType = new CStringValueType(expr);
			
		}
		return specType;
	}
	
	public final JmlStoreRefExpression[]  jmlGroupList(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRefExpression[] self = null;
		
		
		JmlStoreRefExpression name = null;
		ArrayList names = new ArrayList(8);
		
		
		name=jmlGroupName();
		if ( inputState.guessing==0 ) {
			
			names.add( name );
				
		}
		{
		_loop103:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				name=jmlGroupName();
				if ( inputState.guessing==0 ) {
					
					names.add( name );
						
				}
			}
			else {
				break _loop103;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new JmlStoreRefExpression[ names.size() ];
			names.toArray(self);
			
				
		}
		return self;
	}
	
	public final JmlStoreRefExpression  jmlMapsReference(
		
	) throws RecognitionException, TokenStreamException {
		 JmlStoreRefExpression self = null ;
		
		Token  i1 = null;
		Token  j3 = null;
		
		ArrayList namesV = null;
		JmlName name = null;
		TokenReference sourceRef = utility.buildTokenReference();
		
		
		i1 = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			
			name = new JmlName( sourceRef, i1.getText() );
				        namesV = new ArrayList();
				        namesV.add( name );
			
		}
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			{
			int _cnt95=0;
			_loop95:
			do {
				if ((LA(1)==LBRACK)) {
					j3 = LT(1);
					match(LBRACK);
					name=jmlSpecArrayRefExpr( utility.buildTokenReference(j3) );
					match(RBRACK);
					if ( inputState.guessing==0 ) {
						namesV.add( name );
					}
				}
				else {
					if ( _cnt95>=1 ) { break _loop95; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt95++;
			} while (true);
			}
			{
			switch ( LA(1)) {
			case DOT:
			{
				match(DOT);
				jmlMapsMemberRefExpr(namesV);
				break;
			}
			case LITERAL_BS_into:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case DOT:
		{
			match(DOT);
			jmlMapsMemberRefExpr(namesV);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    JmlName[] names = new JmlName[ namesV.size() ];
				    namesV.toArray( names );
				    
				    self = new JmlStoreRefExpression( sourceRef, names );
			
		}
		return self;
	}
	
	public final JmlName  jmlSpecArrayRefExpr(
		 TokenReference sourceRef 
	) throws RecognitionException, TokenStreamException {
		 JmlName self = null ;
		
		
		JExpression start = null;
		JExpression end = null;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			start=jExpression();
			{
			switch ( LA(1)) {
			case DOT_DOT:
			{
				match(DOT_DOT);
				end=jExpression();
				break;
			}
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
					    if (end == null) {
						self = new JmlName(sourceRef, new JmlSpecExpression( start ));
					    } else {
						self = new JmlName(
						    sourceRef,
						    new JmlSpecExpression( start ),
						    new JmlSpecExpression( end )
						);
						end = null;
					    }
					
			}
			break;
		}
		case STAR:
		{
			match(STAR);
			if ( inputState.guessing==0 ) {
				
					    self = new JmlName(sourceRef, JmlName.SORT_ALL);
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final void jmlMapsMemberRefExpr(
		ArrayList namesV
	) throws RecognitionException, TokenStreamException {
		
		Token  j1 = null;
		Token  j2 = null;
		
		JmlName name = null;
		
		
		switch ( LA(1)) {
		case IDENT:
		{
			j1 = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				name = new JmlName(    
				utility.buildTokenReference(j1), j1.getText() ); 
					        namesV.add( name );
				
			}
			break;
		}
		case STAR:
		{
			j2 = LT(1);
			match(STAR);
			if ( inputState.guessing==0 ) {
				
				name = new JmlName(    
				utility.buildTokenReference(j2), JmlName.SORT_FIELDS );
					        namesV.add( name );
						
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final JmlStoreRefExpression  jmlGroupName(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRefExpression self = null;
		
		Token  s1 = null;
		Token  t1 = null;
		Token  id = null;
		
		TokenReference sourceRef = utility.buildTokenReference();
		JExpression name = null;
		ArrayList namesA = new ArrayList(2);
		
		
		{
		switch ( LA(1)) {
		case LITERAL_super:
		case LITERAL_this:
		{
			{
			switch ( LA(1)) {
			case LITERAL_super:
			{
				s1 = LT(1);
				match(LITERAL_super);
				match(DOT);
				if ( inputState.guessing==0 ) {
					
					namesA.add( new JmlName(utility.buildTokenReference(s1),
								                        JmlName.SORT_SUPER) );
					
				}
				break;
			}
			case LITERAL_this:
			{
				t1 = LT(1);
				match(LITERAL_this);
				match(DOT);
				if ( inputState.guessing==0 ) {
					
					namesA.add( new JmlName(utility.buildTokenReference(t1),
								                        JmlName.SORT_THIS) );
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case IDENT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		id = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			
			namesA.add( new JmlName(utility.buildTokenReference(id),
			id.getText()) );
				
		}
		if ( inputState.guessing==0 ) {
			
				    JmlName[] names = new JmlName[ namesA.size() ];
				    namesA.toArray( names );
				    
				    self = new JmlStoreRefExpression( sourceRef, names );
			
		}
		return self;
	}
	
	public final JmlMethodNameList  jmlMethodNameList(
		
	) throws RecognitionException, TokenStreamException {
		JmlMethodNameList nameList=null;
		
		
		TokenReference sourceRef = utility.buildTokenReference();
		ArrayList nameV = null;
		JmlMethodName name = null;
		JmlMethodName[] names = null;
		
		
		name=jmlMethodName();
		if ( inputState.guessing==0 ) {
			
				    nameV = new ArrayList();
				    nameV.add( name );
				
		}
		{
		_loop116:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				name=jmlMethodName();
				if ( inputState.guessing==0 ) {
					nameV.add( name );
				}
			}
			else {
				break _loop116;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    names = new JmlMethodName[ nameV.size() ];
				    nameV.toArray( names );
				    nameList = new JmlMethodNameList(sourceRef, names);
				
		}
		return nameList;
	}
	
	public final JmlStoreRefExpression  jmlStoreRefExpression(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRefExpression self = null;
		
		Token  i1 = null;
		Token  i2 = null;
		Token  i3 = null;
		
		ArrayList namesV = null;
		JmlName name = null;
		TokenReference sourceRef = utility.buildTokenReference();
		
		
		{
		switch ( LA(1)) {
		case IDENT:
		{
			i1 = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				name = new JmlName( sourceRef, i1.getText() );
			}
			break;
		}
		case LITERAL_super:
		{
			i2 = LT(1);
			match(LITERAL_super);
			if ( inputState.guessing==0 ) {
				name =
						new JmlName( sourceRef, JmlName.SORT_SUPER );
			}
			break;
		}
		case LITERAL_this:
		{
			i3 = LT(1);
			match(LITERAL_this);
			if ( inputState.guessing==0 ) {
				name =
						new JmlName( sourceRef, JmlName.SORT_THIS );
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    namesV = new ArrayList();
				    namesV.add( name );
				
		}
		{
		_loop143:
		do {
			if ((LA(1)==DOT||LA(1)==LBRACK)) {
				name=jmlStoreRefNameSuffix();
				if ( inputState.guessing==0 ) {
					namesV.add( name );
				}
			}
			else {
				break _loop143;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    JmlName[] names = new JmlName[ namesV.size() ];
				    namesV.toArray( names );
				    
				    self = new JmlStoreRefExpression( sourceRef, names );
				
		}
		return self;
	}
	
	public final JmlSpecExpression  jmlSpecExpression(
		
	) throws RecognitionException, TokenStreamException {
		JmlSpecExpression self = null;
		
		
		JExpression expr = null;
		
		
		expr=jExpression();
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecExpression( expr );
				
		}
		return self;
	}
	
	public final JmlSpecExpression[]  jmlSpecExpressionList(
		
	) throws RecognitionException, TokenStreamException {
		JmlSpecExpression[] self = null;
		
		
		ArrayList specArrayList = null;
		JmlSpecExpression spec = null;
		
		
		spec=jmlSpecExpression();
		if ( inputState.guessing==0 ) {
			
				    specArrayList = new ArrayList();
				    specArrayList.add( spec );
				
		}
		{
		_loop294:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				spec=jmlSpecExpression();
				if ( inputState.guessing==0 ) {
					specArrayList.add( spec );
				}
			}
			else {
				break _loop294;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecExpression[ specArrayList.size() ];
				    specArrayList.toArray( self );
				    
				
		}
		return self;
	}
	
	public final JmlMethodName  jmlMethodName(
		
	) throws RecognitionException, TokenStreamException {
		JmlMethodName self = null;
		
		Token  i1 = null;
		Token  i2 = null;
		Token  i3 = null;
		Token  j2 = null;
		Token  j3 = null;
		Token  j4 = null;
		
		StringBuffer methodRef = new StringBuffer();
		TokenReference sourceRef = utility.buildTokenReference();
		boolean isConstructorRef = false;
		CType[] paramTypes = null;
		CType type = null;
		ArrayList namesV = null;
		JmlName name = null;
		boolean hasDisambigList = false;
		CUniverse elem_univ = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_super:
		case LITERAL_this:
		case IDENT:
		{
			{
			switch ( LA(1)) {
			case LITERAL_super:
			{
				i1 = LT(1);
				match(LITERAL_super);
				if ( inputState.guessing==0 ) {
					name = new JmlName(
								utility.buildTokenReference(i1), JmlName.SORT_SUPER);
				}
				break;
			}
			case LITERAL_this:
			{
				i2 = LT(1);
				match(LITERAL_this);
				if ( inputState.guessing==0 ) {
					name = new JmlName(
								utility.buildTokenReference(i2), JmlName.SORT_THIS);
				}
				break;
			}
			case IDENT:
			{
				i3 = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					name = new JmlName(
								utility.buildTokenReference(i3), i3.getText());
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
						namesV = new ArrayList();
						namesV.add( name );
					
			}
			{
			_loop122:
			do {
				if ((LA(1)==DOT)) {
					match(DOT);
					{
					switch ( LA(1)) {
					case LITERAL_this:
					{
						j2 = LT(1);
						match(LITERAL_this);
						if ( inputState.guessing==0 ) {
							name = new JmlName(
										    utility.buildTokenReference(j2),
										    JmlName.SORT_THIS);
						}
						break;
					}
					case IDENT:
					{
						j3 = LT(1);
						match(IDENT);
						if ( inputState.guessing==0 ) {
							name = new JmlName(
										    utility.buildTokenReference(j3), j3.getText());
							
						}
						break;
					}
					case STAR:
					{
						j4 = LT(1);
						match(STAR);
						if ( inputState.guessing==0 ) {
							name = new JmlName(
							utility.buildTokenReference(j4), JmlName.SORT_WILDCARD );
							
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					if ( inputState.guessing==0 ) {
						namesV.add( name );
					}
				}
				else {
					break _loop122;
				}
				
			} while (true);
			}
			break;
		}
		case LITERAL_new:
		{
			match(LITERAL_new);
			{
			switch ( LA(1)) {
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			{
				elem_univ=jUniverseType();
				break;
			}
			case IDENT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			type=jClassTypeSpec(elem_univ, null);
			if ( inputState.guessing==0 ) {
				isConstructorRef = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			match(LPAREN);
			if ( inputState.guessing==0 ) {
				hasDisambigList = true;
			}
			{
			switch ( LA(1)) {
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_short:
			case LITERAL_void:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			{
				paramTypes=jmlParamDisambigList();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			break;
		}
		case COMMA:
		case RPAREN:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    if (paramTypes == null && hasDisambigList) {
						paramTypes = new CType[0];
				    }
				    if (isConstructorRef) {
						self = new JmlConstructorName( sourceRef, type, paramTypes );
				    } else {
						JmlName[] names = new JmlName[ namesV.size() ];
						namesV.toArray( names );
					
						self = new JmlMethodName( sourceRef, names, paramTypes );
				    }
				
		}
		return self;
	}
	
	public final CUniverse  jUniverseType(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case LITERAL_peer:
		case LITERAL_U_peer:
		{
			universe=jUniversePeerSpec();
			break;
		}
		case LITERAL_rep:
		case LITERAL_U_rep:
		{
			universe=jUniverseRepSpec();
			break;
		}
		case LITERAL_readonly:
		case LITERAL_U_readonly:
		{
			universe=jUniverseReadonlySpec();
			if ( inputState.guessing==0 ) {
				
				utility.reportTrouble(
				new PositionedError(
				sourceRef, 
				CUniverseMessages.READONLY_FORBIDDEN_HERE, null));
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CClassType  jClassTypeSpec(
		CUniverse elem_univ, CUniverse array_univ
	) throws RecognitionException, TokenStreamException {
		CClassType self = null;
		
		
		int bounds = 0 ;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		self=jTypeName(elem_univ);
		{
		_loop464:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop464;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			// WMD: added the additional checks for the universe modifiers
			if (bounds > 0) {
			if( elem_univ != null && array_univ == null ) {
			array_univ = CUniverseImplicitPeer.getUniverse();
			
			utility.reportTrouble(new CWarning(sourceRef, 
			CUniverseMessages.ARRAY_WITH_NO_UNIVERSE,
			null));
			}
			
			if( elem_univ != null &&
			(elem_univ instanceof CUniverseRep) ) {
			utility.reportTrouble(new PositionedError(sourceRef, 
			CUniverseMessages.ARRAY_WITH_REP_ELEM_FORBIDDEN,
			null));
			}
			
			self = new CArrayType(self, bounds, array_univ);
			} else {
			if( elem_univ != null && array_univ != null &&
			// ignore if the array universe was implicitly added
			// this makes the cast expression easier
			!(array_univ instanceof CUniverseImplicitPeer) ) {
			utility.reportTrouble(
			new PositionedError(
			sourceRef, 
			CUniverseMessages.NONARRAY_WITH_TWO_UNIVERSES_FORBIDDEN, null));
			
			}
			}
			
		}
		return self;
	}
	
	public final CType[]  jmlParamDisambigList(
		
	) throws RecognitionException, TokenStreamException {
		CType[] types = null;
		
		
		ArrayList typesV = null;
		CType type = null;
		
		
		type=jmlParamDisambig();
		if ( inputState.guessing==0 ) {
			
				    typesV = new ArrayList();
				    typesV.add( type );
				
		}
		{
		_loop128:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				type=jmlParamDisambig();
				if ( inputState.guessing==0 ) {
					typesV.add( type );
				}
			}
			else {
				break _loop128;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    types = new CType[ typesV.size() ];
				    typesV.toArray( types );
				    
				
		}
		return types;
	}
	
	public final CType  jmlParamDisambig(
		
	) throws RecognitionException, TokenStreamException {
		CType type = null;
		
		Token  id = null;
		
		int bounds = 0;
		
		
		type=jTypeSpec();
		{
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			{
			_loop132:
			do {
				if ((LA(1)==LBRACK)) {
					match(LBRACK);
					match(RBRACK);
					if ( inputState.guessing==0 ) {
						bounds += 1;
					}
				}
				else {
					break _loop132;
				}
				
			} while (true);
			}
			break;
		}
		case COMMA:
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(
			new CWarning(utility.buildTokenReference(id), 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(
			new CWarning(utility.buildTokenReference(id),
			MjcMessages.OLD_STYLE_ARRAY_BOUNDS));
			}
			type = new CArrayType(type, bounds, null);
				    }
				
		}
		return type;
	}
	
	public final JmlStoreRef  jmlStoreRef(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRef self = null;
		
		Token  i = null;
		
		TokenReference sourceRef = utility.buildTokenReference();
		JmlSpecExpression specExpression = null;
		CType type = null;
		JmlStoreRefExpression storeRefExpression = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_super:
		case LITERAL_this:
		case IDENT:
		{
			self=jmlStoreRefExpression();
			break;
		}
		case INFORMAL_DESC:
		{
			i = LT(1);
			match(INFORMAL_DESC);
			if ( inputState.guessing==0 ) {
				
						self = new JmlInformalStoreRef( sourceRef, i.getText() );
					
			}
			break;
		}
		case LITERAL_BS_everything:
		case LITERAL_BS_not_specified:
		case LITERAL_BS_nothing:
		{
			self=jmlStoreRefKeyword();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JmlStoreRefKeyword  jmlStoreRefKeyword(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRefKeyword self = null;
		
		
		int keywordType = 0;
		TokenReference sourceRef = utility.buildTokenReference();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_BS_nothing:
		{
			match(LITERAL_BS_nothing);
			if ( inputState.guessing==0 ) {
				keywordType = JmlStoreRefKeyword.NOTHING;
			}
			break;
		}
		case LITERAL_BS_everything:
		{
			match(LITERAL_BS_everything);
			if ( inputState.guessing==0 ) {
				keywordType = JmlStoreRefKeyword.EVERYTHING;
			}
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			if ( inputState.guessing==0 ) {
				keywordType = JmlStoreRefKeyword.NOT_SPECIFIED;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			self = new JmlStoreRefKeyword( sourceRef, keywordType );
		}
		return self;
	}
	
	public final JmlStoreRef[]  jmlStoreRefList(
		
	) throws RecognitionException, TokenStreamException {
		JmlStoreRef[] self = null;
		
		
		ArrayList refsV = null;
		JmlStoreRef ref = null;
		
		
		ref=jmlStoreRef();
		if ( inputState.guessing==0 ) {
			
				    refsV = new ArrayList();
				    refsV.add( ref );
				
		}
		{
		_loop139:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				ref=jmlStoreRef();
				if ( inputState.guessing==0 ) {
					refsV.add( ref );
				}
			}
			else {
				break _loop139;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlStoreRef[ refsV.size() ];
				    refsV.toArray( self );
				    
				
		}
		return self;
	}
	
	public final JmlName  jmlStoreRefNameSuffix(
		
	) throws RecognitionException, TokenStreamException {
		 JmlName self = null ;
		
		Token  j1 = null;
		Token  j2 = null;
		Token  j3 = null;
		Token  j4 = null;
		
		if ((LA(1)==DOT) && (LA(2)==IDENT)) {
			match(DOT);
			j1 = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				self = new JmlName(
				utility.buildTokenReference(j1), j1.getText() );
				
			}
		}
		else if ((LA(1)==DOT) && (LA(2)==LITERAL_this)) {
			match(DOT);
			j2 = LT(1);
			match(LITERAL_this);
			if ( inputState.guessing==0 ) {
				
				self = new JmlName(
				utility.buildTokenReference(j2), JmlName.SORT_THIS );
				
			}
		}
		else if ((LA(1)==LBRACK)) {
			j3 = LT(1);
			match(LBRACK);
			self=jmlSpecArrayRefExpr( utility.buildTokenReference(j3) );
			match(RBRACK);
		}
		else if ((LA(1)==DOT) && (LA(2)==STAR)) {
			match(DOT);
			j4 = LT(1);
			match(STAR);
			if ( inputState.guessing==0 ) {
				
				self = new JmlName(
				utility.buildTokenReference(j4), JmlName.SORT_FIELDS );
						
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		return self;
	}
	
	public final JExpression  jExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		self=jAssignmentExpression();
		return self;
	}
	
	public final JmlSpecification  jmlSpecification(
		long mods
	) throws RecognitionException, TokenStreamException {
		 JmlSpecification self = null ;
		
		
		JmlSpecCase specCases[] = null;
		JmlRedundantSpec redundant = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_extract:
		case LITERAL_forall:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_instance:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_query:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_secret:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			specCases=jmlSpecCaseSeq(mods);
			{
			switch ( LA(1)) {
			case LITERAL_for_example:
			case LITERAL_implies_that:
			{
				redundant=jmlRedundantSpec();
				break;
			}
			case LITERAL_abstract:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_final:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_native:
			case LITERAL_private:
			case LITERAL_protected:
			case LITERAL_public:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_pure:
			case LITERAL_short:
			case LITERAL_static:
			case LITERAL_strictfp:
			case LITERAL_synchronized:
			case LITERAL_transient:
			case LITERAL_void:
			case LITERAL_volatile:
			case LCURLY:
			case LT:
			case SEMI:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			case LITERAL_code_bigint_math:
			case LITERAL_code_java_math:
			case LITERAL_code_safe_math:
			case LITERAL_constructor:
			case LITERAL_extract:
			case LITERAL_ghost:
			case LITERAL_helper:
			case LITERAL_initializer:
			case LITERAL_instance:
			case LITERAL_method:
			case LITERAL_model:
			case LITERAL_monitored:
			case LITERAL_non_null:
			case LITERAL_non_null_by_default:
			case LITERAL_nullable:
			case LITERAL_nullable_by_default:
			case LITERAL_query:
			case LITERAL_secret:
			case LITERAL_spec_bigint_math:
			case LITERAL_spec_java_math:
			case LITERAL_spec_protected:
			case LITERAL_spec_public:
			case LITERAL_spec_safe_math:
			case LITERAL_static_initializer:
			case LITERAL_uninitialized:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				self = new JmlSpecification(sourceRef, specCases, 
				redundant);
				
			}
			break;
		}
		case LITERAL_for_example:
		case LITERAL_implies_that:
		{
			redundant=jmlRedundantSpec();
			if ( inputState.guessing==0 ) {
				
					        if (mods != 0 ) {
						        utility.reportTrouble( new PositionedError(
						    	    utility.buildTokenReference(),
						    	    JmlMessages.REDUNDANT_SPEC_MODIFIERS ));
					        }
				self = new JmlSpecification(sourceRef, redundant);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlExtendingSpecification  jmlExtendingSpecification(
		
	) throws RecognitionException, TokenStreamException {
		 JmlExtendingSpecification self = null ;
		
		
		JmlSpecification spec = null;
		
		
		match(LITERAL_also);
		spec=jmlSpecification(0);
		if ( inputState.guessing==0 ) {
			
				    // In order to preserve the fact that this spec
				    // began with 'also', we need to convert this
				    // to a JmlExtendingSpecification - per the grammar
				    self = new JmlExtendingSpecification(spec);
				
		}
		return self;
	}
	
	public final JmlSpecCase[]  jmlSpecCaseSeq(
		long mods
	) throws RecognitionException, TokenStreamException {
		JmlSpecCase[] self = null ;
		
		
		ArrayList cases = new ArrayList();
		JmlSpecCase c1, c2;
		
		
		c1=jmlSpecCase(mods);
		if ( inputState.guessing==0 ) {
			cases.add(c1);
		}
		{
		_loop152:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				c2=jmlSpecCase(0);
				if ( inputState.guessing==0 ) {
					cases.add(c2);
				}
			}
			else {
				break _loop152;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecCase[cases.size()];
				    cases.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlRedundantSpec  jmlRedundantSpec(
		
	) throws RecognitionException, TokenStreamException {
		 JmlRedundantSpec self = null ;
		
		
		JmlSpecCase implications[] = null;
		JmlExample examples[] = null;
		TokenReference sourceRef = utility.buildTokenReference( );
		
		
		switch ( LA(1)) {
		case LITERAL_implies_that:
		{
			{
			implications=jmlImplications();
			{
			switch ( LA(1)) {
			case LITERAL_for_example:
			{
				examples=jmlExamples();
				break;
			}
			case LITERAL_abstract:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_final:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_native:
			case LITERAL_private:
			case LITERAL_protected:
			case LITERAL_public:
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_pure:
			case LITERAL_short:
			case LITERAL_static:
			case LITERAL_strictfp:
			case LITERAL_synchronized:
			case LITERAL_transient:
			case LITERAL_void:
			case LITERAL_volatile:
			case LCURLY:
			case LT:
			case SEMI:
			case IDENT:
			case LITERAL_BS_TYPE:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			case LITERAL_code_bigint_math:
			case LITERAL_code_java_math:
			case LITERAL_code_safe_math:
			case LITERAL_constructor:
			case LITERAL_extract:
			case LITERAL_ghost:
			case LITERAL_helper:
			case LITERAL_initializer:
			case LITERAL_instance:
			case LITERAL_method:
			case LITERAL_model:
			case LITERAL_monitored:
			case LITERAL_non_null:
			case LITERAL_non_null_by_default:
			case LITERAL_nullable:
			case LITERAL_nullable_by_default:
			case LITERAL_query:
			case LITERAL_secret:
			case LITERAL_spec_bigint_math:
			case LITERAL_spec_java_math:
			case LITERAL_spec_protected:
			case LITERAL_spec_public:
			case LITERAL_spec_safe_math:
			case LITERAL_static_initializer:
			case LITERAL_uninitialized:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				self = new JmlRedundantSpec( sourceRef, implications, examples );
				
			}
			break;
		}
		case LITERAL_for_example:
		{
			examples=jmlExamples();
			if ( inputState.guessing==0 ) {
				
				self = new JmlRedundantSpec( sourceRef, null, examples );
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlSpecCase  jmlSpecCase(
		long mods
	) throws RecognitionException, TokenStreamException {
		JmlSpecCase self = null ;
		
		
		long moreMods = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_forall:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			self=jmlGenericSpecCase(false);
			if ( inputState.guessing==0 ) {
				
				// lightweight specification
				
					    if (mods != 0) {
						utility.reportTrouble( new PositionedError(
							self.getTokenReference(),
							JmlMessages.GENERIC_SPEC_CASE_MODIFIERS ));
					    }
					
			}
			break;
		}
		case LITERAL_abstract:
		case LITERAL_final:
		case LITERAL_native:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_pure:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_synchronized:
		case LITERAL_transient:
		case LITERAL_volatile:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_code:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_extract:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_instance:
		case LITERAL_model:
		case LITERAL_model_program:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_query:
		case LITERAL_secret:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		{
			if ( inputState.guessing==0 ) {
				
				TokenReference sourceRef = utility.buildTokenReference();
				if (!isPrivacyOrNull(mods)) {
						    utility.reportTrouble( new PositionedError(
							    sourceRef,
						    	JmlMessages.BAD_PRIVACY_MODIFIER ));
					    }
				
			}
			moreMods=jModifiers();
			if ( inputState.guessing==0 ) {
				
				TokenReference sourceRef = utility.buildTokenReference();
				if (!isPrivacyOrNull(moreMods)) {
						        utility.reportTrouble( new PositionedError(
							        sourceRef,
							        JmlMessages.BAD_PRIVACY_MODIFIER ));
					        }
				
				if ((mods & moreMods) != 0) {
						        utility.reportTrouble( new PositionedError(
						        	sourceRef,
						        	JmlMessages.MULTIPLE_PRIVACY_MODIFIER ));
				}
				
				mods |= moreMods;
				
			}
			{
			switch ( LA(1)) {
			case LITERAL_code:
			{
				match(LITERAL_code);
				if ( inputState.guessing==0 ) {
					mods |= Constants.ACC_CODE;
				}
				break;
			}
			case LITERAL_behavior:
			case LITERAL_behaviour:
			case LITERAL_exceptional_behavior:
			case LITERAL_exceptional_behaviour:
			case LITERAL_model_program:
			case LITERAL_normal_behavior:
			case LITERAL_normal_behaviour:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LITERAL_behavior:
			case LITERAL_behaviour:
			case LITERAL_exceptional_behavior:
			case LITERAL_exceptional_behaviour:
			case LITERAL_normal_behavior:
			case LITERAL_normal_behaviour:
			{
				self=jmlHeavyweightSpec(mods);
				break;
			}
			case LITERAL_model_program:
			{
				self=jmlModelProgram(mods);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlGenericSpecCase  jmlGenericSpecCase(
		boolean isInSpecStatement
	) throws RecognitionException, TokenStreamException {
		 JmlGenericSpecCase self = null ;
		
		
		JmlSpecVarDecl v[] = null;
		JmlRequiresClause r[] = null;
		JmlGenericSpecBody b = null;
		TokenReference s = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_forall:
		case LITERAL_old:
		{
			v=jmlSpecVarDecls();
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		{
			{
			r=jmlSpecHeader();
			{
			if ((_tokenSet_16.member(LA(1)))) {
				b=jmlGenericSpecBody(isInSpecStatement);
			}
			else if ((_tokenSet_17.member(LA(1)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			}
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			b=jmlGenericSpecBody(isInSpecStatement);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			self = new JmlGenericSpecCase(s, v, r, b);
			
		}
		return self;
	}
	
	public final JmlHeavyweightSpec  jmlHeavyweightSpec(
		long mods
	) throws RecognitionException, TokenStreamException {
		 JmlHeavyweightSpec self = null ;
		
		
		JmlGenericSpecCase generic = null;
		JmlGeneralSpecCase specCase = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case LITERAL_behavior:
		case LITERAL_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_behavior:
			{
				match(LITERAL_behavior);
				break;
			}
			case LITERAL_behaviour:
			{
				match(LITERAL_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			generic=jmlGenericSpecCase(false);
			if ( inputState.guessing==0 ) {
				
				self = new JmlBehaviorSpec(sourceRef, mods, generic);
				
			}
			break;
		}
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_exceptional_behavior:
			{
				match(LITERAL_exceptional_behavior);
				break;
			}
			case LITERAL_exceptional_behaviour:
			{
				match(LITERAL_exceptional_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlExceptionalSpecCase();
			if ( inputState.guessing==0 ) {
				
				self = new JmlExceptionalBehaviorSpec(sourceRef, mods, specCase);
				
			}
			break;
		}
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_normal_behavior:
			{
				match(LITERAL_normal_behavior);
				break;
			}
			case LITERAL_normal_behaviour:
			{
				match(LITERAL_normal_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlNormalSpecCase();
			if ( inputState.guessing==0 ) {
				
				self = new JmlNormalBehaviorSpec(sourceRef, mods, specCase);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlModelProgram  jmlModelProgram(
		long mods
	) throws RecognitionException, TokenStreamException {
		 JmlModelProgram self = null ;
		
		
		JStatement[] statements;
		ParsingController.TokenWrapper declEnd =
		new ParsingController.TokenWrapper();
		TokenReference sourceRef = utility.buildTokenReference();
		
		
		match(LITERAL_model_program);
		if ( inputState.guessing==0 ) {
			isInModelProgram = true;
		}
		statements=jCompoundStatement(declEnd);
		if ( inputState.guessing==0 ) {
			
				    utility.flushJavadocTokensWithWarning( declEnd );
				    self = new JmlModelProgram( sourceRef, mods, statements );
				    isInModelProgram = false;
				
		}
		return self;
	}
	
	public final JmlSpecCase[]  jmlImplications(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSpecCase[] self = null ;
		
		
		match(LITERAL_implies_that);
		self=jmlSpecCaseSeq(0);
		return self;
	}
	
	public final JmlExample[]  jmlExamples(
		
	) throws RecognitionException, TokenStreamException {
		 JmlExample[] self = null ;
		
		
		ArrayList examples = new ArrayList();
		JmlExample e = null;
		
		
		match(LITERAL_for_example);
		e=jmlExample();
		if ( inputState.guessing==0 ) {
			examples.add(e);
		}
		{
		_loop163:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				e=jmlExample();
				if ( inputState.guessing==0 ) {
					examples.add(e);
				}
			}
			else {
				break _loop163;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlExample[examples.size()];
				    examples.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlExample  jmlExample(
		
	) throws RecognitionException, TokenStreamException {
		 JmlExample self = null ;
		
		
		boolean lightWeighted = true;
		long p = 0;
		JmlSpecVarDecl[] vars = null;
		JmlRequiresClause[] hdr = null;
		JmlSpecBodyClause[] body = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		p=jModifiers();
		if ( inputState.guessing==0 ) {
			
			if (!isPrivacyOrNull(p)) {
					utility.reportTrouble( new PositionedError(
						sourceRef,
						JmlMessages.BAD_PRIVACY_MODIFIER ));
				    }
			
		}
		{
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_example:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_forall:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			{
			{
			switch ( LA(1)) {
			case LITERAL_example:
			{
				match(LITERAL_example);
				if ( inputState.guessing==0 ) {
					lightWeighted = false;
				}
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_forall:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_old:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LITERAL_forall:
			case LITERAL_old:
			{
				vars=jmlSpecVarDecls();
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			{
				hdr=jmlSpecHeader();
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			body=jmlSpecBody();
			}
			if ( inputState.guessing==0 ) {
				
				verifySimpleSpecBody(body);
						if (lightWeighted) {
						    if (p != 0) {
								utility.reportTrouble(new PositionedError(
									sourceRef,
									JmlMessages.LIGHT_WEIGHTED_EXAMPLE_SPEC));
						    }
						    self = new JmlExample(sourceRef, vars, hdr, body);
						} else {
						    self = new JmlExample(sourceRef, p, vars, hdr, body);
						}
				
			}
			break;
		}
		case LITERAL_exceptional_example:
		{
			{
			match(LITERAL_exceptional_example);
			{
			switch ( LA(1)) {
			case LITERAL_forall:
			case LITERAL_old:
			{
				vars=jmlSpecVarDecls();
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			{
				hdr=jmlSpecHeader();
				{
				switch ( LA(1)) {
				case LITERAL_accessible:
				case LITERAL_accessible_redundantly:
				case LITERAL_assignable:
				case LITERAL_assignable_redundantly:
				case LITERAL_breaks:
				case LITERAL_breaks_redundantly:
				case LITERAL_callable:
				case LITERAL_callable_redundantly:
				case LITERAL_captures:
				case LITERAL_captures_redundantly:
				case LITERAL_continues:
				case LITERAL_continues_redundantly:
				case LITERAL_diverges:
				case LITERAL_diverges_redundantly:
				case LITERAL_duration:
				case LITERAL_duration_redundantly:
				case LITERAL_ensures:
				case LITERAL_ensures_redundantly:
				case LITERAL_exsures:
				case LITERAL_exsures_redundantly:
				case LITERAL_measured_by:
				case LITERAL_measured_by_redundantly:
				case LITERAL_modifiable:
				case LITERAL_modifiable_redundantly:
				case LITERAL_modifies:
				case LITERAL_modifies_redundantly:
				case LITERAL_post:
				case LITERAL_post_redundantly:
				case LITERAL_returns:
				case LITERAL_returns_redundantly:
				case LITERAL_signals:
				case LITERAL_signals_only:
				case LITERAL_signals_only_redundantly:
				case LITERAL_signals_redundantly:
				case LITERAL_when:
				case LITERAL_when_redundantly:
				case LITERAL_working_space:
				case LITERAL_working_space_redundantly:
				{
					body=jmlSpecBody();
					break;
				}
				case LITERAL_abstract:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_double:
				case LITERAL_final:
				case LITERAL_float:
				case LITERAL_int:
				case LITERAL_long:
				case LITERAL_native:
				case LITERAL_private:
				case LITERAL_protected:
				case LITERAL_public:
				case LITERAL_peer:
				case LITERAL_readonly:
				case LITERAL_rep:
				case LITERAL_pure:
				case LITERAL_short:
				case LITERAL_static:
				case LITERAL_strictfp:
				case LITERAL_synchronized:
				case LITERAL_transient:
				case LITERAL_void:
				case LITERAL_volatile:
				case LCURLY:
				case LT:
				case SEMI:
				case IDENT:
				case LITERAL_BS_TYPE:
				case LITERAL_BS_bigint:
				case LITERAL_BS_real:
				case LITERAL_U_peer:
				case LITERAL_U_rep:
				case LITERAL_U_readonly:
				case LITERAL_also:
				case LITERAL_code_bigint_math:
				case LITERAL_code_java_math:
				case LITERAL_code_safe_math:
				case LITERAL_constructor:
				case LITERAL_extract:
				case LITERAL_ghost:
				case LITERAL_helper:
				case LITERAL_initializer:
				case LITERAL_instance:
				case LITERAL_method:
				case LITERAL_model:
				case LITERAL_monitored:
				case LITERAL_non_null:
				case LITERAL_non_null_by_default:
				case LITERAL_nullable:
				case LITERAL_nullable_by_default:
				case LITERAL_query:
				case LITERAL_secret:
				case LITERAL_spec_bigint_math:
				case LITERAL_spec_java_math:
				case LITERAL_spec_protected:
				case LITERAL_spec_public:
				case LITERAL_spec_safe_math:
				case LITERAL_static_initializer:
				case LITERAL_uninitialized:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					
					// check if body is exceptional-example-body.
					if (body != null) {
					verifyExceptionalSpecBody(body);
					}
					self = new JmlExceptionalExample(sourceRef,
					p,vars,hdr,body);
					
				}
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				body=jmlSpecBody();
				if ( inputState.guessing==0 ) {
					
					// check if body is exceptional-example-body.
					verifyExceptionalSpecBody(body);
					self = new JmlExceptionalExample(sourceRef,
					p,vars,hdr,body);
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		case LITERAL_normal_example:
		{
			{
			match(LITERAL_normal_example);
			{
			switch ( LA(1)) {
			case LITERAL_forall:
			case LITERAL_old:
			{
				vars=jmlSpecVarDecls();
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LITERAL_pre:
			case LITERAL_pre_redundantly:
			case LITERAL_requires:
			case LITERAL_requires_redundantly:
			{
				hdr=jmlSpecHeader();
				{
				switch ( LA(1)) {
				case LITERAL_accessible:
				case LITERAL_accessible_redundantly:
				case LITERAL_assignable:
				case LITERAL_assignable_redundantly:
				case LITERAL_breaks:
				case LITERAL_breaks_redundantly:
				case LITERAL_callable:
				case LITERAL_callable_redundantly:
				case LITERAL_captures:
				case LITERAL_captures_redundantly:
				case LITERAL_continues:
				case LITERAL_continues_redundantly:
				case LITERAL_diverges:
				case LITERAL_diverges_redundantly:
				case LITERAL_duration:
				case LITERAL_duration_redundantly:
				case LITERAL_ensures:
				case LITERAL_ensures_redundantly:
				case LITERAL_exsures:
				case LITERAL_exsures_redundantly:
				case LITERAL_measured_by:
				case LITERAL_measured_by_redundantly:
				case LITERAL_modifiable:
				case LITERAL_modifiable_redundantly:
				case LITERAL_modifies:
				case LITERAL_modifies_redundantly:
				case LITERAL_post:
				case LITERAL_post_redundantly:
				case LITERAL_returns:
				case LITERAL_returns_redundantly:
				case LITERAL_signals:
				case LITERAL_signals_only:
				case LITERAL_signals_only_redundantly:
				case LITERAL_signals_redundantly:
				case LITERAL_when:
				case LITERAL_when_redundantly:
				case LITERAL_working_space:
				case LITERAL_working_space_redundantly:
				{
					body=jmlSpecBody();
					break;
				}
				case LITERAL_abstract:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_double:
				case LITERAL_final:
				case LITERAL_float:
				case LITERAL_int:
				case LITERAL_long:
				case LITERAL_native:
				case LITERAL_private:
				case LITERAL_protected:
				case LITERAL_public:
				case LITERAL_peer:
				case LITERAL_readonly:
				case LITERAL_rep:
				case LITERAL_pure:
				case LITERAL_short:
				case LITERAL_static:
				case LITERAL_strictfp:
				case LITERAL_synchronized:
				case LITERAL_transient:
				case LITERAL_void:
				case LITERAL_volatile:
				case LCURLY:
				case LT:
				case SEMI:
				case IDENT:
				case LITERAL_BS_TYPE:
				case LITERAL_BS_bigint:
				case LITERAL_BS_real:
				case LITERAL_U_peer:
				case LITERAL_U_rep:
				case LITERAL_U_readonly:
				case LITERAL_also:
				case LITERAL_code_bigint_math:
				case LITERAL_code_java_math:
				case LITERAL_code_safe_math:
				case LITERAL_constructor:
				case LITERAL_extract:
				case LITERAL_ghost:
				case LITERAL_helper:
				case LITERAL_initializer:
				case LITERAL_instance:
				case LITERAL_method:
				case LITERAL_model:
				case LITERAL_monitored:
				case LITERAL_non_null:
				case LITERAL_non_null_by_default:
				case LITERAL_nullable:
				case LITERAL_nullable_by_default:
				case LITERAL_query:
				case LITERAL_secret:
				case LITERAL_spec_bigint_math:
				case LITERAL_spec_java_math:
				case LITERAL_spec_protected:
				case LITERAL_spec_public:
				case LITERAL_spec_safe_math:
				case LITERAL_static_initializer:
				case LITERAL_uninitialized:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					
					// check if body is normal-example-body.
					if (body != null) {
					verifyNormalSpecBody(body);
					}
					self = new JmlNormalExample(sourceRef,p,vars,hdr,body);
					
				}
				break;
			}
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			case LITERAL_assignable:
			case LITERAL_assignable_redundantly:
			case LITERAL_breaks:
			case LITERAL_breaks_redundantly:
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			case LITERAL_captures:
			case LITERAL_captures_redundantly:
			case LITERAL_continues:
			case LITERAL_continues_redundantly:
			case LITERAL_diverges:
			case LITERAL_diverges_redundantly:
			case LITERAL_duration:
			case LITERAL_duration_redundantly:
			case LITERAL_ensures:
			case LITERAL_ensures_redundantly:
			case LITERAL_exsures:
			case LITERAL_exsures_redundantly:
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			case LITERAL_modifiable:
			case LITERAL_modifiable_redundantly:
			case LITERAL_modifies:
			case LITERAL_modifies_redundantly:
			case LITERAL_post:
			case LITERAL_post_redundantly:
			case LITERAL_returns:
			case LITERAL_returns_redundantly:
			case LITERAL_signals:
			case LITERAL_signals_only:
			case LITERAL_signals_only_redundantly:
			case LITERAL_signals_redundantly:
			case LITERAL_when:
			case LITERAL_when_redundantly:
			case LITERAL_working_space:
			case LITERAL_working_space_redundantly:
			{
				body=jmlSpecBody();
				if ( inputState.guessing==0 ) {
					
					// check if body is normal-example-body.
					verifyNormalSpecBody(body);
					self = new JmlNormalExample(sourceRef,p,vars,hdr,body);
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JmlSpecVarDecl[]  jmlSpecVarDecls(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSpecVarDecl[] self = null ;
		
		
		ArrayList decls = new ArrayList();
		JmlSpecVarDecl decl;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_forall:
		{
			{
			int _cnt247=0;
			_loop247:
			do {
				if ((LA(1)==LITERAL_forall)) {
					decl=jmlForAllVarDecl();
					if ( inputState.guessing==0 ) {
						decls.add( decl );
					}
				}
				else {
					if ( _cnt247>=1 ) { break _loop247; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt247++;
			} while (true);
			}
			{
			_loop249:
			do {
				if ((LA(1)==LITERAL_old)) {
					decl=jmlLocalSpecVarDecl();
					if ( inputState.guessing==0 ) {
						decls.add( decl );
					}
				}
				else {
					break _loop249;
				}
				
			} while (true);
			}
			break;
		}
		case LITERAL_old:
		{
			{
			int _cnt251=0;
			_loop251:
			do {
				if ((LA(1)==LITERAL_old)) {
					decl=jmlLocalSpecVarDecl();
					if ( inputState.guessing==0 ) {
						decls.add( decl );
					}
				}
				else {
					if ( _cnt251>=1 ) { break _loop251; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt251++;
			} while (true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecVarDecl[ decls.size() ];
				    decls.toArray( self );
				    
				
		}
		return self;
	}
	
	public final JmlRequiresClause[]  jmlSpecHeader(
		
	) throws RecognitionException, TokenStreamException {
		JmlRequiresClause[] self = null ;
		
		
		ArrayList reqs = new ArrayList();
		JmlRequiresClause r;
		
		
		{
		int _cnt171=0;
		_loop171:
		do {
			if ((_tokenSet_18.member(LA(1)))) {
				r=jmlRequiresClause();
				if ( inputState.guessing==0 ) {
					reqs.add(r);
				}
			}
			else {
				if ( _cnt171>=1 ) { break _loop171; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt171++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlRequiresClause[reqs.size()];
				    reqs.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlGenericSpecBody  jmlGenericSpecBody(
		boolean isInSpecStatement
	) throws RecognitionException, TokenStreamException {
		 JmlGenericSpecBody self = null ;
		
		
		JmlSpecBodyClause simple[] = null;
		JmlGenericSpecCase generic[] = null;
		
		
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			simple=jmlSpecBody();
			if ( inputState.guessing==0 ) {
				
				if (isInSpecStatement) {
				verifySimpleSpecStatementBody(simple);
				} else {
				verifySimpleSpecBody(simple);
				}
				self = new JmlGenericSpecBody(simple);
				
			}
			break;
		}
		case LCURLY_VBAR:
		{
			match(LCURLY_VBAR);
			generic=jmlGenericSpecCaseSeq(isInSpecStatement);
			match(VBAR_RCURLY);
			if ( inputState.guessing==0 ) {
				
				self = new JmlGenericSpecBody(generic);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlRequiresClause  jmlRequiresClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlRequiresClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_requires:
		{
			match(LITERAL_requires);
			break;
		}
		case LITERAL_pre:
		{
			match(LITERAL_pre);
			break;
		}
		case LITERAL_pre_redundantly:
		case LITERAL_requires_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_requires_redundantly:
			{
				match(LITERAL_requires_redundantly);
				break;
			}
			case LITERAL_pre_redundantly:
			{
				match(LITERAL_pre_redundantly);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		case LITERAL_BS_same:
		{
			match(LITERAL_BS_same);
			if ( inputState.guessing==0 ) {
				
				predicate = new JmlPredicateKeyword( sourceRef, 
				Constants.SAME ); 
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlRequiresClause( sourceRef, redundantly, predicate );
				
		}
		return self;
	}
	
	public final JmlSpecBodyClause[]  jmlSpecBody(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSpecBodyClause[] self = null ;
		
		
		ArrayList clauses = new ArrayList();
		JmlSpecBodyClause c;
		int curOrder = JmlSpecBodyClause.PORDER_UNKNOWN;
		
		
		{
		int _cnt178=0;
		_loop178:
		do {
			if ((_tokenSet_19.member(LA(1)))) {
				c=jmlSpecBodyClause();
				if ( inputState.guessing==0 ) {
					
					clauses.add(c);
					if (c.preferredOrder() < curOrder) {
					utility.reportTrouble(
					new CWarning(c.getTokenReference(),
								    JmlMessages.BAD_SPEC_BODY_ORDER,
								    null));
					}
					curOrder = c.preferredOrder();
					
				}
			}
			else {
				if ( _cnt178>=1 ) { break _loop178; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt178++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecBodyClause[clauses.size()];
				    clauses.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlGenericSpecCase[]  jmlGenericSpecCaseSeq(
		boolean isInSpecStatement
	) throws RecognitionException, TokenStreamException {
		JmlGenericSpecCase[] self = null ;
		
		
		ArrayList cases = new ArrayList();
		JmlGenericSpecCase c1, c2;
		
		
		c1=jmlGenericSpecCase(isInSpecStatement);
		if ( inputState.guessing==0 ) {
			cases.add(c1);
		}
		{
		_loop175:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				c2=jmlGenericSpecCase(isInSpecStatement);
				if ( inputState.guessing==0 ) {
					cases.add(c2);
				}
			}
			else {
				break _loop175;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlGenericSpecCase[cases.size()];
				    cases.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlSpecBodyClause  jmlSpecBodyClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSpecBodyClause self = null ;
		
		
		switch ( LA(1)) {
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		{
			self=jmlEnsuresClause();
			break;
		}
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		{
			self=jmlSignalsOnlyClause();
			break;
		}
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_redundantly:
		{
			self=jmlSignalsClause();
			break;
		}
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		{
			self=jmlAssignableClause();
			break;
		}
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		{
			self=jmlCapturesClause();
			break;
		}
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		{
			self=jmlDivergesClause();
			break;
		}
		case LITERAL_when:
		case LITERAL_when_redundantly:
		{
			self=jmlWhenClause();
			break;
		}
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			self=jmlWorkingSpaceClause();
			break;
		}
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		{
			self=jmlDurationClause();
			break;
		}
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		{
			self=jmlContinuesClause();
			break;
		}
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		{
			self=jmlBreaksClause();
			break;
		}
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		{
			self=jmlReturnsClause();
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		{
			self=jmlAccessibleClause();
			break;
		}
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		{
			self=jmlCallableClause();
			break;
		}
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		{
			self=jmlMeasuredClause();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlEnsuresClause  jmlEnsuresClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlEnsuresClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_ensures:
		{
			match(LITERAL_ensures);
			break;
		}
		case LITERAL_post:
		{
			match(LITERAL_post);
			break;
		}
		case LITERAL_ensures_redundantly:
		case LITERAL_post_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_ensures_redundantly:
			{
				match(LITERAL_ensures_redundantly);
				break;
			}
			case LITERAL_post_redundantly:
			{
				match(LITERAL_post_redundantly);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlEnsuresClause( sourceRef, redundantly, predicate );
				
		}
		return self;
	}
	
	public final JmlSignalsOnlyClause  jmlSignalsOnlyClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSignalsOnlyClause self = null ;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		boolean isRedundantly = false;
		CClassType[] exceptions = null;
		boolean nothing = false;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_signals_only:
		{
			match(LITERAL_signals_only);
			break;
		}
		case LITERAL_signals_only_redundantly:
		{
			match(LITERAL_signals_only_redundantly);
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		{
			exceptions=jNameList();
			break;
		}
		case LITERAL_BS_nothing:
		{
			match(LITERAL_BS_nothing);
			if ( inputState.guessing==0 ) {
				nothing = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSignalsOnlyClause(sourceRef, isRedundantly,
			exceptions, nothing);
				
		}
		return self;
	}
	
	public final JmlSignalsClause  jmlSignalsClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlSignalsClause self = null ;
		
		Token  id = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		boolean redundantly = false;
		boolean notSpecified = false;
		JmlPredicate pred = null;
		CType type = null;
		String ident = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_signals:
		{
			match(LITERAL_signals);
			break;
		}
		case LITERAL_signals_redundantly:
		{
			match(LITERAL_signals_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		case LITERAL_exsures:
		{
			match(LITERAL_exsures);
			break;
		}
		case LITERAL_exsures_redundantly:
		{
			match(LITERAL_exsures_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(LPAREN);
		type=jClassTypeSpec(null, null);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				ident = id.getText();
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RPAREN);
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			pred=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			if ( inputState.guessing==0 ) {
				notSpecified = true;
			}
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSignalsClause(sourceRef, redundantly,
					type, ident, pred, notSpecified);
				
		}
		return self;
	}
	
	public final JmlAssignableClause  jmlAssignableClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlAssignableClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate predicate = null;
		JmlStoreRef sref[];
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_assignable:
		{
			match(LITERAL_assignable);
			break;
		}
		case LITERAL_modifiable:
		{
			match(LITERAL_modifiable);
			break;
		}
		case LITERAL_modifies:
		{
			match(LITERAL_modifies);
			break;
		}
		case LITERAL_assignable_redundantly:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_assignable_redundantly:
			{
				match(LITERAL_assignable_redundantly);
				break;
			}
			case LITERAL_modifiable_redundantly:
			{
				match(LITERAL_modifiable_redundantly);
				break;
			}
			case LITERAL_modifies_redundantly:
			{
				match(LITERAL_modifies_redundantly);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		sref=jmlStoreRefList();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			//@ assert sref != null && sref.length > 0;
				    self = new JmlAssignableClause( sourceRef, redundantly, sref );
				
		}
		return self;
	}
	
	public final JmlCapturesClause  jmlCapturesClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlCapturesClause self = null ;
		
		
		boolean redundantly = false;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JmlStoreRef sref[];
		
		
		{
		switch ( LA(1)) {
		case LITERAL_captures:
		{
			match(LITERAL_captures);
			break;
		}
		case LITERAL_captures_redundantly:
		{
			match(LITERAL_captures_redundantly);
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		sref=jmlStoreRefList();
		if ( inputState.guessing==0 ) {
			
			//@ assert sref != null && sref.length > 0;
			self = new JmlCapturesClause( sourceRef, redundantly, sref );
			
		}
		match(SEMI);
		return self;
	}
	
	public final JmlDivergesClause  jmlDivergesClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlDivergesClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_diverges:
		{
			match(LITERAL_diverges);
			break;
		}
		case LITERAL_diverges_redundantly:
		{
			match(LITERAL_diverges_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlDivergesClause( sourceRef, redundantly, predicate );
				
		}
		return self;
	}
	
	public final JmlWhenClause  jmlWhenClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlWhenClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_when:
		{
			match(LITERAL_when);
			break;
		}
		case LITERAL_when_redundantly:
		{
			match(LITERAL_when_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlWhenClause( sourceRef, redundantly, predicate );
				
		}
		return self;
	}
	
	public final JmlWorkingSpaceClause  jmlWorkingSpaceClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlWorkingSpaceClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate pred = null;
		JmlSpecExpression exp = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_working_space:
		{
			match(LITERAL_working_space);
			break;
		}
		case LITERAL_working_space_redundantly:
		{
			match(LITERAL_working_space_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			{
			exp=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case LITERAL_if:
			{
				match(LITERAL_if);
				pred=jmlPredicate();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlWorkingSpaceClause(sourceRef, redundantly, exp, pred);
				
		}
		return self;
	}
	
	public final JmlDurationClause  jmlDurationClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlDurationClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate pred = null;
		JmlSpecExpression exp = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_duration:
		{
			match(LITERAL_duration);
			break;
		}
		case LITERAL_duration_redundantly:
		{
			match(LITERAL_duration_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			{
			exp=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case LITERAL_if:
			{
				match(LITERAL_if);
				pred=jmlPredicate();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlDurationClause(sourceRef, redundantly, exp, pred);
				
		}
		return self;
	}
	
	public final JmlContinuesClause  jmlContinuesClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlContinuesClause self = null ;
		
		Token  id = null;
		
		boolean redundantly = false;
		String label = null;
		JmlPredicate predicate = null;
		boolean isNS = false;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_continues:
		{
			match(LITERAL_continues);
			break;
		}
		case LITERAL_continues_redundantly:
		{
			match(LITERAL_continues_redundantly);
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case R_ARROW:
		{
			match(R_ARROW);
			match(LPAREN);
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				label = id.getText();
			}
			match(RPAREN);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case SEMI:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_not_specified:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			if ( inputState.guessing==0 ) {
				isNS = true;
			}
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlContinuesClause(
			sourceRef, redundantly, label, predicate, isNS );
				
		}
		return self;
	}
	
	public final JmlBreaksClause  jmlBreaksClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlBreaksClause self = null ;
		
		Token  id = null;
		
		boolean redundantly = false;
		String label = null;
		JmlPredicate predicate = null;
		boolean isNS = false;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_breaks:
		{
			match(LITERAL_breaks);
			break;
		}
		case LITERAL_breaks_redundantly:
		{
			match(LITERAL_breaks_redundantly);
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case R_ARROW:
		{
			match(R_ARROW);
			match(LPAREN);
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				label = id.getText();
			}
			match(RPAREN);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case SEMI:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_not_specified:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			if ( inputState.guessing==0 ) {
				isNS = true;
			}
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlBreaksClause(
			sourceRef, redundantly, label, predicate, isNS );
				
		}
		return self;
	}
	
	public final JmlReturnsClause  jmlReturnsClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlReturnsClause self = null ;
		
		
		boolean redundantly = false;
		boolean isNS = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_returns:
		{
			match(LITERAL_returns);
			break;
		}
		case LITERAL_returns_redundantly:
		{
			match(LITERAL_returns_redundantly);
			if ( inputState.guessing==0 ) {
				redundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlPredicate();
			break;
		}
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			if ( inputState.guessing==0 ) {
				isNS = true;
			}
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlReturnsClause(
			sourceRef, redundantly, predicate, isNS );
				
		}
		return self;
	}
	
	public final JmlAccessibleClause  jmlAccessibleClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlAccessibleClause self = null ;
		
		
		boolean redundantly = false;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JmlStoreRef sref[];
		
		
		{
		switch ( LA(1)) {
		case LITERAL_accessible:
		{
			match(LITERAL_accessible);
			break;
		}
		case LITERAL_accessible_redundantly:
		{
			match(LITERAL_accessible_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		sref=jmlStoreRefList();
		if ( inputState.guessing==0 ) {
			
			self = new JmlAccessibleClause( sourceRef, redundantly, sref );
			
		}
		match(SEMI);
		return self;
	}
	
	public final JmlCallableClause  jmlCallableClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlCallableClause self = null ;
		
		
		boolean redundantly = false;
		JmlMethodNameList names = null;
		JmlStoreRefKeyword storeRefKeyword = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_callable:
		{
			match(LITERAL_callable);
			break;
		}
		case LITERAL_callable_redundantly:
		{
			match(LITERAL_callable_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_new:
		case LITERAL_super:
		case LITERAL_this:
		case IDENT:
		{
			names=jmlMethodNameList();
			if ( inputState.guessing==0 ) {
				
				self = new JmlCallableClause( sourceRef, redundantly, names );
				
			}
			break;
		}
		case LITERAL_BS_everything:
		case LITERAL_BS_not_specified:
		case LITERAL_BS_nothing:
		{
			storeRefKeyword=jmlStoreRefKeyword();
			if ( inputState.guessing==0 ) {
				
				names = new JmlMethodNameList( sourceRef, storeRefKeyword );
				self = new JmlCallableClause( sourceRef, redundantly, names );
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		return self;
	}
	
	public final JmlMeasuredClause  jmlMeasuredClause(
		
	) throws RecognitionException, TokenStreamException {
		 JmlMeasuredClause self = null ;
		
		
		boolean redundantly = false;
		JmlPredicate pred = null;
		JmlSpecExpression exp = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_measured_by:
		{
			match(LITERAL_measured_by);
			break;
		}
		case LITERAL_measured_by_redundantly:
		{
			match(LITERAL_measured_by_redundantly);
			if ( inputState.guessing==0 ) {
				
				redundantly = true;
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_BS_not_specified:
		{
			match(LITERAL_BS_not_specified);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			{
			exp=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case LITERAL_if:
			{
				match(LITERAL_if);
				pred=jmlPredicate();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlMeasuredClause(sourceRef, redundantly, exp, pred);
				
		}
		return self;
	}
	
	public final JmlExceptionalSpecCase  jmlExceptionalSpecCase(
		
	) throws RecognitionException, TokenStreamException {
		 JmlExceptionalSpecCase self = null ;
		
		
		JmlSpecVarDecl v[] = null;
		JmlRequiresClause h[] = null;
		JmlExceptionalSpecBody b = null;
		TokenReference s = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_forall:
		case LITERAL_old:
		{
			v=jmlSpecVarDecls();
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		{
			{
			h=jmlSpecHeader();
			{
			if ((_tokenSet_16.member(LA(1)))) {
				b=jmlExceptionalSpecBody();
			}
			else if ((_tokenSet_17.member(LA(1)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			}
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			b=jmlExceptionalSpecBody();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			self = new JmlExceptionalSpecCase(s, v, h, b);
			
		}
		return self;
	}
	
	public final JmlNormalSpecCase  jmlNormalSpecCase(
		
	) throws RecognitionException, TokenStreamException {
		 JmlNormalSpecCase self = null ;
		
		
		JmlSpecVarDecl vars[] = null;
		JmlRequiresClause hdr[] = null;
		JmlNormalSpecBody body = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_forall:
		case LITERAL_old:
		{
			vars=jmlSpecVarDecls();
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		{
			{
			hdr=jmlSpecHeader();
			{
			if ((_tokenSet_16.member(LA(1)))) {
				body=jmlNormalSpecBody();
			}
			else if ((_tokenSet_17.member(LA(1)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			}
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			body=jmlNormalSpecBody();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			self = new JmlNormalSpecCase(sourceRef, vars, hdr, body);
			
		}
		return self;
	}
	
	public final JmlExceptionalSpecBody  jmlExceptionalSpecBody(
		
	) throws RecognitionException, TokenStreamException {
		 JmlExceptionalSpecBody self = null ;
		
		
		JmlSpecBodyClause specClauses[] = null;
		JmlGeneralSpecCase specCases[] = null;
		
		
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			specClauses=jmlSpecBody();
			if ( inputState.guessing==0 ) {
				
				verifyExceptionalSpecBody(specClauses);
				self = new JmlExceptionalSpecBody(specClauses);
				
			}
			break;
		}
		case LCURLY_VBAR:
		{
			match(LCURLY_VBAR);
			specCases=jmlExceptionalSpecCaseSeq();
			match(VBAR_RCURLY);
			if ( inputState.guessing==0 ) {
				
				self = new JmlExceptionalSpecBody(specCases);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlGeneralSpecCase[]  jmlExceptionalSpecCaseSeq(
		
	) throws RecognitionException, TokenStreamException {
		JmlGeneralSpecCase[] self = null ;
		
		
		ArrayList cases = new ArrayList();
		JmlExceptionalSpecCase c1, c2;
		
		
		c1=jmlExceptionalSpecCase();
		if ( inputState.guessing==0 ) {
			cases.add(c1);
		}
		{
		_loop192:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				c2=jmlExceptionalSpecCase();
				if ( inputState.guessing==0 ) {
					cases.add(c2);
				}
			}
			else {
				break _loop192;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlGeneralSpecCase[cases.size()];
				    cases.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlNormalSpecBody  jmlNormalSpecBody(
		
	) throws RecognitionException, TokenStreamException {
		 JmlNormalSpecBody self = null ;
		
		
		JmlSpecBodyClause specClauses[] = null;
		JmlGeneralSpecCase specCases[] = null;
		
		
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			specClauses=jmlSpecBody();
			if ( inputState.guessing==0 ) {
				
				verifyNormalSpecBody(specClauses);
				self = new JmlNormalSpecBody(specClauses);
				
			}
			break;
		}
		case LCURLY_VBAR:
		{
			match(LCURLY_VBAR);
			specCases=jmlNormalSpecCaseSeq();
			match(VBAR_RCURLY);
			if ( inputState.guessing==0 ) {
				
				self = new JmlNormalSpecBody(specCases);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlGeneralSpecCase[]  jmlNormalSpecCaseSeq(
		
	) throws RecognitionException, TokenStreamException {
		JmlGeneralSpecCase[] self = null ;
		
		
		ArrayList cases = new ArrayList();
		JmlNormalSpecCase c1, c2;
		
		
		c1=jmlNormalSpecCase();
		if ( inputState.guessing==0 ) {
			cases.add(c1);
		}
		{
		_loop201:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				c2=jmlNormalSpecCase();
				if ( inputState.guessing==0 ) {
					cases.add(c2);
				}
			}
			else {
				break _loop201;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlGeneralSpecCase[cases.size()];
				    cases.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JmlCodeContract  jmlCodeContract(
		long mods
	) throws RecognitionException, TokenStreamException {
		 JmlCodeContract self = null ;
		
		
		JmlSpecBodyClause c = null;
		ArrayList accessibleClauses = new ArrayList();
		ArrayList callableClauses = new ArrayList();
		ArrayList measuredClauses = new ArrayList();
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LITERAL_code_contract);
		{
		{
		int _cnt205=0;
		_loop205:
		do {
			switch ( LA(1)) {
			case LITERAL_accessible:
			case LITERAL_accessible_redundantly:
			{
				c=jmlAccessibleClause();
				if ( inputState.guessing==0 ) {
					accessibleClauses.add(c);
				}
				break;
			}
			case LITERAL_callable:
			case LITERAL_callable_redundantly:
			{
				c=jmlCallableClause();
				if ( inputState.guessing==0 ) {
					callableClauses.add(c);
				}
				break;
			}
			case LITERAL_measured_by:
			case LITERAL_measured_by_redundantly:
			{
				c=jmlMeasuredClause();
				if ( inputState.guessing==0 ) {
					measuredClauses.add(c);
				}
				break;
			}
			default:
			{
				if ( _cnt205>=1 ) { break _loop205; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			}
			_cnt205++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			JmlAccessibleClause[] acs 
			= new JmlAccessibleClause[accessibleClauses.size()];
			accessibleClauses.toArray(acs);
			
			JmlCallableClause[] ccs 
			= new JmlCallableClause[callableClauses.size()];
			callableClauses.toArray(ccs);
			
			JmlMeasuredClause[] mcs
			= new JmlMeasuredClause[measuredClauses.size()];
			measuredClauses.toArray(mcs);
			
			self = new JmlCodeContract(sourceRef, mods, acs, ccs, mcs);
			
		}
		}
		return self;
	}
	
	public final JmlForAllVarDecl  jmlForAllVarDecl(
		
	) throws RecognitionException, TokenStreamException {
		 JmlForAllVarDecl self = null ;
		
		Token  s = null;
		
		JmlVariableDefinition[] quantifiedVarDecls;
		
		
		s = LT(1);
		match(LITERAL_forall);
		quantifiedVarDecls=jmlQuantifiedVarDecls();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlForAllVarDecl(
					utility.buildTokenReference( s ), quantifiedVarDecls );
				
		}
		return self;
	}
	
	public final JmlLetVarDecl  jmlLocalSpecVarDecl(
		
	) throws RecognitionException, TokenStreamException {
		 JmlLetVarDecl self = null ;
		
		
		long mods = 0;
		CType type;
		JVariableDefinition[] specVariableDeclarators;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LITERAL_old);
		{
		boolean synPredMatched256 = false;
		if (((_tokenSet_20.member(LA(1))) && (_tokenSet_15.member(LA(2))))) {
			int _m256 = mark();
			synPredMatched256 = true;
			inputState.guessing++;
			try {
				{
				jmlNullityModifier();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched256 = false;
			}
			rewind(_m256);
inputState.guessing--;
		}
		if ( synPredMatched256 ) {
			mods=jmlNullityModifier();
		}
		else if ((_tokenSet_15.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		type=jTypeSpec();
		specVariableDeclarators=jmlSpecVariableDeclarators(mods, type);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlLetVarDecl( sourceRef, specVariableDeclarators );
				
		}
		return self;
	}
	
	public final JmlVariableDefinition[]  jmlQuantifiedVarDecls(
		
	) throws RecognitionException, TokenStreamException {
		JmlVariableDefinition[] self = null;
		
		Token  id1 = null;
		Token  id2 = null;
		
		CType baseType;
		CType type;
		long mods = 0;
		int bounds = 0;
		ArrayList decls = null;
		
		
		{
		boolean synPredMatched313 = false;
		if (((_tokenSet_20.member(LA(1))) && (_tokenSet_15.member(LA(2))))) {
			int _m313 = mark();
			synPredMatched313 = true;
			inputState.guessing++;
			try {
				{
				jmlNullityModifier();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched313 = false;
			}
			rewind(_m313);
inputState.guessing--;
		}
		if ( synPredMatched313 ) {
			mods=jmlNullityModifier();
			baseType=jTypeSpec();
		}
		else if ((_tokenSet_15.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
			baseType=jTypeSpec();
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		id1 = LT(1);
		match(IDENT);
		{
		_loop315:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop315;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(
			new CWarning(utility.buildTokenReference(id1), 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(
			new CWarning(utility.buildTokenReference(id1),
			MjcMessages.OLD_STYLE_ARRAY_BOUNDS, null));
			}
			type = new CArrayType(baseType, bounds, null);
				    } else {
			type = baseType;
				    }
				    bounds = 0;
				    decls = new ArrayList();
				    decls.add(
					new JmlVariableDefinition(
					    utility.buildTokenReference( id1 ), mods, type,
					    id1.getText(), null ));
				
		}
		{
		_loop319:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				id2 = LT(1);
				match(IDENT);
				{
				_loop318:
				do {
					if ((LA(1)==LBRACK)) {
						match(LBRACK);
						match(RBRACK);
						if ( inputState.guessing==0 ) {
							bounds += 1;
						}
					}
					else {
						break _loop318;
					}
					
				} while (true);
				}
				if ( inputState.guessing==0 ) {
					
							if (bounds > 0) {
					if( utility.getCompiler().universeChecks() ) {
					utility.reportTrouble(
					new CWarning(utility.buildTokenReference(id2), 
					CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
					null));
					} else {
					utility.reportTrouble(
					new CWarning(utility.buildTokenReference(id2),
					MjcMessages.OLD_STYLE_ARRAY_BOUNDS, null));
					}
							    type = new CArrayType(baseType, bounds, null);
							} else {
							    type = baseType;
							}
							bounds = 0;
							decls.add(
							    new JmlVariableDefinition(
								utility.buildTokenReference( id2 ), mods, type,
								id2.getText(), null ));
						
				}
			}
			else {
				break _loop319;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlVariableDefinition[ decls.size() ];
				    decls.toArray( self );
				    
				
		}
		return self;
	}
	
	public final long  jmlNullityModifier(
		
	) throws RecognitionException, TokenStreamException {
		long mods = 0;
		
		
		switch ( LA(1)) {
		case LITERAL_non_null:
		{
			match(LITERAL_non_null);
			if ( inputState.guessing==0 ) {
				mods = Constants.ACC_NON_NULL;
			}
			break;
		}
		case LITERAL_nullable:
		{
			match(LITERAL_nullable);
			if ( inputState.guessing==0 ) {
				mods = Constants.ACC_NULLABLE;
			}
			break;
		}
		default:
			if (((LA(1)==IDENT) && (_tokenSet_15.member(LA(2))))&&( "non_null".equals(LT(1).getText()) )) {
				match(IDENT);
				if ( inputState.guessing==0 ) {
					// Interpret the identifier as a nullity modifier.
						    mods = Constants.ACC_NON_NULL; 
						
				}
			}
			else if (((LA(1)==IDENT) && (_tokenSet_15.member(LA(2))))&&( "nullable".equals(LT(1).getText()) )) {
				match(IDENT);
				if ( inputState.guessing==0 ) {
					// Interpret the identifier as a nullity modifier.
						    mods = Constants.ACC_NULLABLE; 
						
				}
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return mods;
	}
	
	public final JVariableDefinition[]  jmlSpecVariableDeclarators(
		long mods, CType type
	) throws RecognitionException, TokenStreamException {
		JVariableDefinition[] self = null;
		
		
		ArrayList vars = new ArrayList();
		JVariableDefinition	decl;
		
		
		decl=jmlSpecVariableDeclarator(mods, type);
		if ( inputState.guessing==0 ) {
			vars.add(decl);
		}
		{
		_loop324:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				decl=jmlSpecVariableDeclarator(mods, type);
				if ( inputState.guessing==0 ) {
					vars.add(decl);
				}
			}
			else {
				break _loop324;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlVariableDefinition[vars.size()];
				    self = (JVariableDefinition[]) vars.toArray(self);
				    
				
		}
		return self;
	}
	
	public final CClassType[]  jNameList(
		
	) throws RecognitionException, TokenStreamException {
		CClassType[] self = null;
		
		
		//String    name;
		CClassType name;
		ArrayList    vect = new ArrayList();
		
		
		name=jTypeName(null);
		if ( inputState.guessing==0 ) {
			vect.add(name);
		}
		{
		_loop646:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				name=jTypeName(null);
				if ( inputState.guessing==0 ) {
					vect.add(name);
				}
			}
			else {
				break _loop646;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new CClassType[vect.size()];
			self = (CClassType[]) vect.toArray(self);
			
			
		}
		return self;
	}
	
	public final JExpression  jmlPrimary(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  label = null;
		Token  infDesc = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JmlSpecExpression specExpression;
		JExpression expression;
		JmlStoreRef[] storeRefList;
		JmlMethodNameList names = null;
		JmlSpecExpression[] specExpressionList;
		CType type = null;
		JmlStoreRefExpression storeRefExpression = null;
		
		
		switch ( LA(1)) {
		case LITERAL_BS_result:
		{
			match(LITERAL_BS_result);
			if ( inputState.guessing==0 ) {
				self = new JmlResultExpression( sourceRef );
			}
			break;
		}
		case LITERAL_BS_old:
		{
			match(LITERAL_BS_old);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				label = LT(1);
				match(IDENT);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlOldExpression( sourceRef, 
				specExpression,
				(label!=null? label.getText(): null) );
				
			}
			break;
		}
		case LITERAL_BS_pre:
		{
			match(LITERAL_BS_pre);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlPreExpression( sourceRef, specExpression );
			}
			break;
		}
		case LITERAL_BS_not_modified:
		{
			match(LITERAL_BS_not_modified);
			match(LPAREN);
			storeRefList=jmlStoreRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlNotModifiedExpression( sourceRef, storeRefList );
			}
			break;
		}
		case LITERAL_BS_only_accessed:
		{
			match(LITERAL_BS_only_accessed);
			match(LPAREN);
			storeRefList=jmlStoreRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlOnlyAccessedExpression( sourceRef, storeRefList );
			}
			break;
		}
		case LITERAL_BS_not_assigned:
		{
			match(LITERAL_BS_not_assigned);
			match(LPAREN);
			storeRefList=jmlStoreRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlNotAssignedExpression( sourceRef, storeRefList );
			}
			break;
		}
		case LITERAL_BS_only_called:
		{
			match(LITERAL_BS_only_called);
			match(LPAREN);
			names=jmlMethodNameList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlOnlyCalledExpression( sourceRef, names );
			}
			break;
		}
		case LITERAL_BS_only_captured:
		{
			match(LITERAL_BS_only_captured);
			match(LPAREN);
			storeRefList=jmlStoreRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlOnlyCapturedExpression( sourceRef, storeRefList );
			}
			break;
		}
		case LITERAL_BS_only_assigned:
		{
			match(LITERAL_BS_only_assigned);
			match(LPAREN);
			storeRefList=jmlStoreRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlOnlyAssignedExpression( sourceRef, storeRefList );
			}
			break;
		}
		case LITERAL_BS_fresh:
		{
			match(LITERAL_BS_fresh);
			match(LPAREN);
			specExpressionList=jmlSpecExpressionList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlFreshExpression( sourceRef, specExpressionList );
			}
			break;
		}
		case LITERAL_BS_working_space:
		{
			match(LITERAL_BS_working_space);
			match(LPAREN);
			expression=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlWorkingSpaceExpression( sourceRef, expression );
			}
			break;
		}
		case LITERAL_BS_space:
		{
			match(LITERAL_BS_space);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlSpaceExpression( sourceRef, specExpression );
			}
			break;
		}
		case LITERAL_BS_duration:
		{
			match(LITERAL_BS_duration);
			match(LPAREN);
			expression=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlDurationExpression( sourceRef, expression );
			}
			break;
		}
		case LITERAL_BS_reach:
		{
			match(LITERAL_BS_reach);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				type=jClassTypeSpec(null, null);
				{
				switch ( LA(1)) {
				case COMMA:
				{
					match(COMMA);
					storeRefExpression=jmlStoreRefExpression();
					break;
				}
				case RPAREN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlReachExpression( sourceRef, specExpression, type,
								storeRefExpression );
				/*
				* The following isn't used, but is kept as an example
				* of how to deprecate something, if you want to make
				* something deprecated.  It can be deleted when you have
				* something you really want to deprecate.
				*
				* utility.reportTrouble(
				*     new CWarning( sourceRef,
				*                   JmlMessages.DEPRECATED_REACH ));
				*/
				
			}
			break;
		}
		case INFORMAL_DESC:
		{
			infDesc = LT(1);
			match(INFORMAL_DESC);
			if ( inputState.guessing==0 ) {
				self = new JmlInformalExpression( sourceRef, infDesc.getText() );
			}
			break;
		}
		case LITERAL_BS_nonnullelements:
		{
			match(LITERAL_BS_nonnullelements);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlNonNullElementsExpression( sourceRef,
								specExpression );
			}
			break;
		}
		case LITERAL_BS_typeof:
		{
			match(LITERAL_BS_typeof);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlTypeOfExpression( sourceRef, specExpression );
			}
			break;
		}
		case LITERAL_BS_elemtype:
		{
			match(LITERAL_BS_elemtype);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlElemTypeExpression( sourceRef, specExpression );
			}
			break;
		}
		case LITERAL_BS_type:
		{
			match(LITERAL_BS_type);
			match(LPAREN);
			type=jTypeSpec();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlTypeExpression( sourceRef, type );
			}
			break;
		}
		case LITERAL_BS_lockset:
		{
			match(LITERAL_BS_lockset);
			if ( inputState.guessing==0 ) {
				self = new JmlLockSetExpression( sourceRef );
			}
			break;
		}
		case LITERAL_BS_max:
		{
			match(LITERAL_BS_max);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlMaxExpression(sourceRef,specExpression);
			}
			break;
		}
		case LITERAL_BS_is_initialized:
		{
			match(LITERAL_BS_is_initialized);
			match(LPAREN);
			type=jClassTypeSpec(null, null);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlIsInitializedExpression( sourceRef, type );
			}
			break;
		}
		case LITERAL_BS_invariant_for:
		{
			match(LITERAL_BS_invariant_for);
			match(LPAREN);
			specExpression=jmlSpecExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JmlInvariantForExpression( sourceRef, specExpression );
			}
			break;
		}
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		{
			self=jmlWarnExpression();
			break;
		}
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_java_math:
		case LITERAL_BS_safe_math:
		{
			self=jmlMathModeExpression();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  jmlWarnExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op1 = null;
		Token  op2 = null;
		Token  op3 = null;
		Token  op4 = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JExpression expr = null;
		
		
		switch ( LA(1)) {
		case LITERAL_BS_warn:
		{
			op1 = LT(1);
			match(LITERAL_BS_warn);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op1.getText(), expr, true);
			}
			break;
		}
		case LITERAL_BS_warn_op:
		{
			op2 = LT(1);
			match(LITERAL_BS_warn_op);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op2.getText(), expr, true, true);
			}
			break;
		}
		case LITERAL_BS_nowarn:
		{
			op3 = LT(1);
			match(LITERAL_BS_nowarn);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op3.getText(), expr, false);
			}
			break;
		}
		case LITERAL_BS_nowarn_op:
		{
			op4 = LT(1);
			match(LITERAL_BS_nowarn_op);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op4.getText(), expr, false, true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  jmlMathModeExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op1 = null;
		Token  op2 = null;
		Token  op3 = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JExpression expr = null;
		
		
		switch ( LA(1)) {
		case LITERAL_BS_java_math:
		{
			op1 = LT(1);
			match(LITERAL_BS_java_math);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJMathModeExpression(sourceRef, op1.getText(), expr, Constants.AMID_JAVA_MATH);
			}
			break;
		}
		case LITERAL_BS_safe_math:
		{
			op2 = LT(1);
			match(LITERAL_BS_safe_math);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJMathModeExpression(sourceRef, op2.getText(), expr, Constants.AMID_SAFE_MATH);
			}
			break;
		}
		case LITERAL_BS_bigint_math:
		{
			op3 = LT(1);
			match(LITERAL_BS_bigint_math);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJMathModeExpression(sourceRef, op3.getText(), expr, Constants.AMID_BIGINT_MATH);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  jmlSetComprehension(
		CType type
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  start = null;
		Token  id = null;
		
		long mods = 0;
		CType memberType;
		int bounds = 0;
		JmlPredicate pred;
		JExpression supersetPred;
		
		
		start = LT(1);
		match(LCURLY);
		{
		boolean synPredMatched303 = false;
		if (((_tokenSet_20.member(LA(1))) && (_tokenSet_15.member(LA(2))))) {
			int _m303 = mark();
			synPredMatched303 = true;
			inputState.guessing++;
			try {
				{
				jmlNullityModifier();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched303 = false;
			}
			rewind(_m303);
inputState.guessing--;
		}
		if ( synPredMatched303 ) {
			mods=jmlNullityModifier();
		}
		else if ((_tokenSet_15.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		memberType=jTypeSpec();
		id = LT(1);
		match(IDENT);
		{
		_loop305:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop305;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(
			new CWarning(utility.buildTokenReference(id), 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(
					            new CWarning(utility.buildTokenReference(id),
						MjcMessages.OLD_STYLE_ARRAY_BOUNDS));
			}
			memberType = new CArrayType(memberType, bounds, null);
				    }
				
		}
		match(BOR);
		supersetPred=jPostfixExpression();
		match(LAND);
		pred=jmlPredicate();
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSetComprehension(
					utility.buildTokenReference(start), mods, type,
					memberType, id.getText(), supersetPred, pred );
				
		}
		return self;
	}
	
	public final JExpression  jPostfixExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  ident = null;
		Token  l = null;
		
		int        bounds = 0;
		JExpression    expr;
		JExpression[]    args = null;
		
		
		self=jPrimaryExpression();
		{
		_loop617:
		do {
			switch ( LA(1)) {
			case DOT:
			{
				match(DOT);
				{
				switch ( LA(1)) {
				case IDENT:
				{
					ident = LT(1);
					match(IDENT);
					if ( inputState.guessing==0 ) {
						self = new JNameExpression(utility.buildTokenReference(), 
						self, ident.getText(), null );
					}
					{
					switch ( LA(1)) {
					case LPAREN:
					{
						l = LT(1);
						match(LPAREN);
						args=jArgList();
						match(RPAREN);
						if ( inputState.guessing==0 ) {
							self = new JMethodCallExpression(utility.buildTokenReference(), 
							self, args);
						}
						break;
					}
					case LITERAL_for:
					case LITERAL_if:
					case LITERAL_instanceof:
					case ASSIGN:
					case BAND:
					case BAND_ASSIGN:
					case BOR:
					case BOR_ASSIGN:
					case BSR:
					case BSR_ASSIGN:
					case BXOR:
					case BXOR_ASSIGN:
					case COLON:
					case COMMA:
					case DEC:
					case DOT:
					case EQUAL:
					case GE:
					case GT:
					case INC:
					case LAND:
					case LBRACK:
					case LE:
					case LOR:
					case LT:
					case MINUS:
					case MINUS_ASSIGN:
					case NOT_EQUAL:
					case PERCENT:
					case PERCENT_ASSIGN:
					case PLUS:
					case PLUS_ASSIGN:
					case QUESTION:
					case RBRACK:
					case RCURLY:
					case RPAREN:
					case SEMI:
					case SL:
					case SLASH:
					case SLASH_ASSIGN:
					case SL_ASSIGN:
					case SR:
					case SR_ASSIGN:
					case STAR:
					case STAR_ASSIGN:
					case IDENT:
					case DOT_DOT:
					case IMPLIES:
					case BACKWARD_IMPLIES:
					case EQUIV:
					case NOT_EQUIV:
					case SUBTYPE_OF:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					break;
				}
				case LITERAL_this:
				{
					match(LITERAL_this);
					if ( inputState.guessing==0 ) {
						self = new JThisExpression(utility.buildTokenReference(), 
						self);
					}
					break;
				}
				case LITERAL_super:
				{
					match(LITERAL_super);
					self=jSuperSuffix(new JSuperExpression(utility.buildTokenReference(), self));
					break;
				}
				case LITERAL_new:
				{
					self=jNewExpression(self);
					break;
				}
				case LITERAL_resend:
				{
					match(LITERAL_resend);
					self=mjResendSuffix(self);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case LBRACK:
			{
				match(LBRACK);
				expr=jExpression();
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					self = new JArrayAccessExpression(utility.buildTokenReference(), 
					self, expr);
				}
				break;
			}
			default:
			{
				break _loop617;
			}
			}
		} while (true);
		}
		{
		switch ( LA(1)) {
		case INC:
		{
			match(INC);
			if ( inputState.guessing==0 ) {
				self = new JPostfixExpression(utility.buildTokenReference(), Constants.OPE_POSTINC, self);
			}
			break;
		}
		case DEC:
		{
			match(DEC);
			if ( inputState.guessing==0 ) {
				self = new JPostfixExpression(utility.buildTokenReference(), Constants.OPE_POSTDEC, self);
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case LITERAL_instanceof:
		case ASSIGN:
		case BAND:
		case BAND_ASSIGN:
		case BOR:
		case BOR_ASSIGN:
		case BSR:
		case BSR_ASSIGN:
		case BXOR:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case EQUAL:
		case GE:
		case GT:
		case LAND:
		case LE:
		case LOR:
		case LT:
		case MINUS:
		case MINUS_ASSIGN:
		case NOT_EQUAL:
		case PERCENT:
		case PERCENT_ASSIGN:
		case PLUS:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SL:
		case SLASH:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR:
		case SR_ASSIGN:
		case STAR:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		case IMPLIES:
		case BACKWARD_IMPLIES:
		case EQUIV:
		case NOT_EQUIV:
		case SUBTYPE_OF:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JmlSpecQuantifiedExpression  jmlSpecQuantifiedExprRest(
		TokenReference sourceRef
	) throws RecognitionException, TokenStreamException {
		JmlSpecQuantifiedExpression self = null;
		
		
		int oper = -1;
		JmlVariableDefinition[] quantifiedVarDecls;
		JmlSpecExpression predicate = null;
		JmlSpecExpression specExpression = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_BS_forall:
		{
			match(LITERAL_BS_forall);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_FORALL;
			}
			break;
		}
		case LITERAL_BS_exists:
		{
			match(LITERAL_BS_exists);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_EXISTS;
			}
			break;
		}
		case LITERAL_BS_max:
		{
			match(LITERAL_BS_max);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_MAX;
			}
			break;
		}
		case LITERAL_BS_min:
		{
			match(LITERAL_BS_min);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_MIN;
			}
			break;
		}
		case LITERAL_BS_num_of:
		{
			match(LITERAL_BS_num_of);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_NUM_OF;
			}
			break;
		}
		case LITERAL_BS_product:
		{
			match(LITERAL_BS_product);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_PRODUCT;
			}
			break;
		}
		case LITERAL_BS_sum:
		{
			match(LITERAL_BS_sum);
			if ( inputState.guessing==0 ) {
				oper = Constants.OPE_SUM;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		quantifiedVarDecls=jmlQuantifiedVarDecls();
		match(SEMI);
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			predicate=jmlSpecExpression();
			{
			switch ( LA(1)) {
			case SEMI:
			{
				match(SEMI);
				specExpression=jmlSpecExpression();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
						if (specExpression == null) {
						    // really the predicate is optional
						    specExpression = predicate;
						    predicate = null;
						}
					
			}
			break;
		}
		case SEMI:
		{
			match(SEMI);
			specExpression=jmlSpecExpression();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecQuantifiedExpression( sourceRef, oper,
					quantifiedVarDecls,
					predicate == null ? null : new JmlPredicate( predicate ),
					specExpression );
				
		}
		return self;
	}
	
	public final long  jmlNonNullNullityModifier(
		
	) throws RecognitionException, TokenStreamException {
		long mods = 0;
		
		
		if (((LA(1)==IDENT))&&( "non_null".equals(LT(1).getText()) )) {
			match(IDENT);
			if ( inputState.guessing==0 ) {
				// Interpret the identifier as a nullity modifier.
					    mods = Constants.ACC_NON_NULL; 
					
			}
		}
		else if ((LA(1)==LITERAL_non_null)) {
			match(LITERAL_non_null);
			if ( inputState.guessing==0 ) {
				mods = Constants.ACC_NON_NULL;
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		return mods;
	}
	
	public final JVariableDefinition  jmlSpecVariableDeclarator(
		long mods, CType type
	) throws RecognitionException, TokenStreamException {
		JVariableDefinition self = null;
		
		Token  ident = null;
		
		int	bounds = 0;
		JExpression	expr = null;
		TokenReference sourceRef = utility.buildTokenReference();
		
		
		ident = LT(1);
		match(IDENT);
		{
		_loop327:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop327;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case ASSIGN:
		{
			match(ASSIGN);
			expr=jmlSpecInitializer();
			break;
		}
		case COMMA:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(new CWarning(sourceRef, 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, null));
			} else {
			utility.reportTrouble(new CWarning(sourceRef,
			MjcMessages.OLD_STYLE_ARRAY_BOUNDS, null));
			}
			type = new CArrayType(type, bounds, null);
				    }
				    self = new JmlVariableDefinition(sourceRef, mods, type, ident.getText(), expr);
				
		}
		return self;
	}
	
	public final JExpression  jmlSpecInitializer(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			self=jmlSpecExpression();
			break;
		}
		case LCURLY:
		{
			self=jmlSpecArrayInitializer();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JArrayInitializer  jmlSpecArrayInitializer(
		
	) throws RecognitionException, TokenStreamException {
		JArrayInitializer self = null;
		
		
		JExpression		expr = null;
		ArrayList		vect = new ArrayList();
		TokenReference	sourceRef = utility.buildTokenReference();
		
		
		match(LCURLY);
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LCURLY:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			expr=jmlSpecInitializer();
			if ( inputState.guessing==0 ) {
				vect.add(expr);
			}
			{
			_loop332:
			do {
				if ((LA(1)==COMMA) && (_tokenSet_21.member(LA(2)))) {
					match(COMMA);
					expr=jmlSpecInitializer();
					if ( inputState.guessing==0 ) {
						vect.add(expr);
					}
				}
				else {
					break _loop332;
				}
				
			} while (true);
			}
			break;
		}
		case COMMA:
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case COMMA:
		{
			match(COMMA);
			if ( inputState.guessing==0 ) {
				
						utility.reportTrouble(
						    new CWarning(sourceRef,
							MjcMessages.STRAY_COMMA, null));
					
			}
			break;
		}
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
				    self = new JArrayInitializer(sourceRef,
					(JExpression[]) vect.toArray(new JExpression[0]));
				    
				
		}
		return self;
	}
	
	public final JStatement  jStatement(
		
	) throws RecognitionException, TokenStreamException {
		JStatement self = null;
		
		
		
		
		switch ( LA(1)) {
		case LITERAL_abstract:
		case LITERAL_assert:
		case LITERAL_boolean:
		case LITERAL_break:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_class:
		case LITERAL_continue:
		case LITERAL_do:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_final:
		case LITERAL_float:
		case LITERAL_for:
		case LITERAL_if:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_native:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_private:
		case LITERAL_protected:
		case LITERAL_public:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_pure:
		case LITERAL_resend:
		case LITERAL_return:
		case LITERAL_short:
		case LITERAL_static:
		case LITERAL_strictfp:
		case LITERAL_super:
		case LITERAL_switch:
		case LITERAL_synchronized:
		case LITERAL_this:
		case LITERAL_throw:
		case LITERAL_transient:
		case LITERAL_true:
		case LITERAL_try:
		case LITERAL_void:
		case LITERAL_volatile:
		case LITERAL_while:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LCURLY:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case SEMI:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_TYPE:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case LITERAL_code_bigint_math:
		case LITERAL_code_java_math:
		case LITERAL_code_safe_math:
		case LITERAL_decreases:
		case LITERAL_decreases_redundantly:
		case LITERAL_decreasing:
		case LITERAL_decreasing_redundantly:
		case LITERAL_extract:
		case LITERAL_ghost:
		case LITERAL_helper:
		case LITERAL_instance:
		case LITERAL_loop_invariant:
		case LITERAL_loop_invariant_redundantly:
		case LITERAL_maintaining:
		case LITERAL_maintaining_redundantly:
		case LITERAL_model:
		case LITERAL_monitored:
		case LITERAL_non_null:
		case LITERAL_non_null_by_default:
		case LITERAL_nullable:
		case LITERAL_nullable_by_default:
		case LITERAL_query:
		case LITERAL_secret:
		case LITERAL_spec_bigint_math:
		case LITERAL_spec_java_math:
		case LITERAL_spec_protected:
		case LITERAL_spec_public:
		case LITERAL_spec_safe_math:
		case LITERAL_uninitialized:
		case INFORMAL_DESC:
		{
			self=mjStatement();
			if ( inputState.guessing==0 ) {
				
				if (self instanceof JExpressionStatement) {
				JExpressionStatement exprStmt = (JExpressionStatement)self;
				JExpression expr = exprStmt.expr();
				if (expr instanceof JAssignmentExpression) {
				self = new JmlAssignmentStatement(exprStmt);
				}
				}
				
			}
			break;
		}
		case LITERAL_hence_by:
		case LITERAL_hence_by_redundantly:
		{
			self=jmlHenceByStatement();
			break;
		}
		case LITERAL_assert_redundantly:
		case AFFIRM:
		{
			self=jmlAssertStatement();
			break;
		}
		case LITERAL_assume:
		case LITERAL_assume_redundantly:
		{
			self=jmlAssumeStatement();
			break;
		}
		case LITERAL_debug:
		{
			self=jmlDebugStatement();
			break;
		}
		case LITERAL_set:
		{
			self=jmlSetStatement();
			break;
		}
		case LITERAL_refining:
		{
			self=jmlRefiningStatement();
			break;
		}
		case LITERAL_unreachable:
		{
			self=jmlUnreachableStatement();
			break;
		}
		case LITERAL_abrupt_behavior:
		case LITERAL_abrupt_behaviour:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_choose:
		case LITERAL_choose_if:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_invariant:
		case LITERAL_invariant_redundantly:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		{
			self=jmlModelProgStatement();
			if ( inputState.guessing==0 ) {
				
					    if (!isInModelProgram) {
						utility.reportTrouble(
						    new PositionedError( self.getTokenReference(),
							JmlMessages.ILLEGAL_MODEL_PROG_STATEMENT ));
					    }
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JStatement  mjStatement(
		
	) throws RecognitionException, TokenStreamException {
		JStatement self = null;
		
		
		JExpression        expr;
		JStatement[]        stmts;
		JTypeDeclarationType    type;
		JavaStyleComment[]    comments = utility.getStatementComment();
		TokenReference    sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case LCURLY:
		{
			stmts=jCompoundStatement(null);
			if ( inputState.guessing==0 ) {
				self = new JBlock(sourceRef, stmts, comments);
			}
			break;
		}
		case LITERAL_class:
		{
			type=jClassDefinition(0,null);
			if ( inputState.guessing==0 ) {
				self = new JTypeDeclarationStatement(type.getTokenReference(), type);
			}
			break;
		}
		case LITERAL_if:
		{
			self=jIfStatement();
			break;
		}
		case LITERAL_do:
		case LITERAL_for:
		case LITERAL_while:
		case LITERAL_decreases:
		case LITERAL_decreases_redundantly:
		case LITERAL_decreasing:
		case LITERAL_decreasing_redundantly:
		case LITERAL_loop_invariant:
		case LITERAL_loop_invariant_redundantly:
		case LITERAL_maintaining:
		case LITERAL_maintaining_redundantly:
		{
			self=jLoopStatement();
			break;
		}
		case LITERAL_break:
		{
			self=jBreakStatement();
			break;
		}
		case LITERAL_continue:
		{
			self=jContinueStatement();
			break;
		}
		case LITERAL_return:
		{
			self=jReturnStatement();
			break;
		}
		case LITERAL_switch:
		{
			self=jSwitchStatement();
			break;
		}
		case LITERAL_try:
		{
			self=jTryBlock();
			break;
		}
		case LITERAL_throw:
		{
			self=jThrowStatement();
			break;
		}
		case LITERAL_assert:
		{
			self=jAssertStatement();
			break;
		}
		case SEMI:
		{
			match(SEMI);
			if ( inputState.guessing==0 ) {
				self = new JEmptyStatement(sourceRef, comments);
			}
			break;
		}
		default:
			if ((LA(1)==LITERAL_final) && (LA(2)==LITERAL_class)) {
				match(LITERAL_final);
				type=jClassDefinition(org.multijava.mjc.Constants.ACC_FINAL,null);
				if ( inputState.guessing==0 ) {
					self = new JTypeDeclarationStatement(type.getTokenReference(), type);
				}
			}
			else if ((LA(1)==LITERAL_abstract) && (LA(2)==LITERAL_class)) {
				match(LITERAL_abstract);
				type=jClassDefinition(org.multijava.mjc.Constants.ACC_ABSTRACT,null);
				if ( inputState.guessing==0 ) {
					self = new JTypeDeclarationStatement(type.getTokenReference(), type);
				}
			}
			else {
				boolean synPredMatched537 = false;
				if (((_tokenSet_22.member(LA(1))) && (_tokenSet_23.member(LA(2))))) {
					int _m537 = mark();
					synPredMatched537 = true;
					inputState.guessing++;
					try {
						{
						jModifiers();
						jTypeSpec();
						match(IDENT);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched537 = false;
					}
					rewind(_m537);
inputState.guessing--;
				}
				if ( synPredMatched537 ) {
					self=jDeclaration();
					match(SEMI);
				}
				else if ((_tokenSet_24.member(LA(1))) && (_tokenSet_25.member(LA(2)))) {
					expr=jExpression();
					match(SEMI);
					if ( inputState.guessing==0 ) {
						self = new JExpressionStatement(sourceRef, expr, comments);
					}
				}
				else if ((LA(1)==IDENT) && (LA(2)==COLON)) {
					self=jLabeledStatement();
				}
				else if ((LA(1)==LITERAL_synchronized) && (LA(2)==LPAREN)) {
					self=jSynchronizedStatement();
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}}
			return self;
		}
		
	public final JmlHenceByStatement  jmlHenceByStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlHenceByStatement self = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		boolean isRedundantly = false;
		JmlPredicate predicate;
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_hence_by:
		{
			match(LITERAL_hence_by);
			break;
		}
		case LITERAL_hence_by_redundantly:
		{
			match(LITERAL_hence_by_redundantly);
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate=jmlPredicate();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlHenceByStatement( sourceRef, isRedundantly,
					predicate, comments );
				
		}
		return self;
	}
	
	public final JmlAssertStatement  jmlAssertStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlAssertStatement self = null;
		
		Token  s1 = null;
		Token  s2 = null;
		
		JExpression expression = null;
		JExpression throwMessage = null;
		JavaStyleComment[] comments = utility.getStatementComment();
		JmlPredicate predicate = null;
		
		
		switch ( LA(1)) {
		case AFFIRM:
		{
			s1 = LT(1);
			match(AFFIRM);
			predicate=jmlPredicate();
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				throwMessage=jExpression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
					    self = new JmlAssertStatement( utility.buildTokenReference(s1),
						false, predicate, throwMessage, comments );
					
			}
			break;
		}
		case LITERAL_assert_redundantly:
		{
			s2 = LT(1);
			match(LITERAL_assert_redundantly);
			predicate=jmlPredicate();
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				throwMessage=jExpression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
					    self = new JmlAssertStatement( utility.buildTokenReference(s2),
						true, predicate, throwMessage, comments );
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlAssumeStatement  jmlAssumeStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlAssumeStatement self = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		boolean isRedundantly = false;
		JmlPredicate predicate;
		JExpression throwMessage = null;
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_assume:
		{
			match(LITERAL_assume);
			break;
		}
		case LITERAL_assume_redundantly:
		{
			match(LITERAL_assume_redundantly);
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate=jmlPredicate();
		{
		switch ( LA(1)) {
		case COLON:
		{
			match(COLON);
			throwMessage=jExpression();
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlAssumeStatement(
					sourceRef, isRedundantly, predicate, throwMessage, comments );
				
		}
		return self;
	}
	
	public final JmlDebugStatement  jmlDebugStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlDebugStatement self = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JExpression expression;
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		match(LITERAL_debug);
		expression=jExpression();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlDebugStatement( sourceRef, expression, comments );
				
		}
		return self;
	}
	
	public final JmlSetStatement  jmlSetStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlSetStatement self = null;
		
		Token  s = null;
		
		JExpression assignmentExpression;
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		s = LT(1);
		match(LITERAL_set);
		assignmentExpression=jAssignmentExpression();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSetStatement(
					utility.buildTokenReference( s ), assignmentExpression,
					comments );
				
		}
		return self;
	}
	
	public final JmlRefiningStatement  jmlRefiningStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlRefiningStatement self = null;
		
		Token  r = null;
		
		JmlGeneralSpecCase gencase = null;
		JmlSpecStatement specstmt = null;
		JStatement body;
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		r = LT(1);
		match(LITERAL_refining);
		{
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_forall:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_old:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			gencase=jmlGenericSpecCase(true);
			break;
		}
		case LITERAL_abrupt_behavior:
		case LITERAL_abrupt_behaviour:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		{
			specstmt=jmlSpecStatement();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		body=jStatement();
		if ( inputState.guessing==0 ) {
			
			if (gencase != null) {
			specstmt = new JmlSpecStatement(
			utility.buildTokenReference( r ), gencase, comments);
			}
			//@ assert specstmt != null;
				    self = new JmlRefiningStatement(
					utility.buildTokenReference( r ), specstmt, gencase != null, 
			body,
			comments );
				
		}
		return self;
	}
	
	public final JmlUnreachableStatement  jmlUnreachableStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlUnreachableStatement self = null;
		
		Token  s = null;
		
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		s = LT(1);
		match(LITERAL_unreachable);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlUnreachableStatement(
					utility.buildTokenReference( s ), comments );
				
		}
		return self;
	}
	
	public final JmlModelProgStatement  jmlModelProgStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlModelProgStatement self = null;
		
		
		
		
		switch ( LA(1)) {
		case LITERAL_choose:
		{
			self=jmlNondeterministicChoice();
			break;
		}
		case LITERAL_choose_if:
		{
			self=jmlNondeterministicIf();
			break;
		}
		case LITERAL_invariant:
		case LITERAL_invariant_redundantly:
		{
			self=jmlInvariantStatement();
			break;
		}
		case LITERAL_abrupt_behavior:
		case LITERAL_abrupt_behaviour:
		case LITERAL_behavior:
		case LITERAL_behaviour:
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		{
			self=jmlSpecStatement();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JVariableDeclarationStatement  jDeclaration(
		
	) throws RecognitionException, TokenStreamException {
		JVariableDeclarationStatement self = null;
		
		
		long         mods;
		CType        type;
		JVariableDefinition[] vars;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		mods=jModifiers();
		type=jTypeSpec();
		vars=jVariableDefinitions(mods, type);
		if ( inputState.guessing==0 ) {
			
			if ( Utils.hasOtherFlags(mods,
			Constants.ACC_FINAL
			| Constants.ACC_GHOST
			| Constants.ACC_NON_NULL
			| Constants.ACC_NULLABLE) ) {
					        utility.reportTrouble(
						        new PositionedError(sourceRef,
						            JmlMessages.INVALID_LOCAL_MODIFIER,
			utility.getModifierNames(mods)));
			}
			if ( Utils.hasFlag(mods, Constants.ACC_GHOST) ) {
			// this declaration is in an annotation
					        for (int i = 0; i < vars.length; i++) {
						        vars[i] = new JmlVariableDefinition(
							                vars[i].getTokenReference(), mods, type, 
			vars[i].ident(), vars[i].expr() );
					        }
					    }
			self = new JVariableDeclarationStatement(
			sourceRef, vars, utility.getStatementComment() );
			
		}
		return self;
	}
	
	public final JStatement  jLoopStatement(
		
	) throws RecognitionException, TokenStreamException {
		JStatement self = null;
		
		
		JmlLoopInvariant[] invs = null;
		JmlVariantFunction[] vars = null;
		JStatement stmt = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		switch ( LA(1)) {
		case LITERAL_decreases:
		case LITERAL_decreases_redundantly:
		case LITERAL_decreasing:
		case LITERAL_decreasing_redundantly:
		case LITERAL_loop_invariant:
		case LITERAL_loop_invariant_redundantly:
		case LITERAL_maintaining:
		case LITERAL_maintaining_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_loop_invariant:
			case LITERAL_loop_invariant_redundantly:
			case LITERAL_maintaining:
			case LITERAL_maintaining_redundantly:
			{
				invs=jmlLoopInvariantList();
				{
				switch ( LA(1)) {
				case LITERAL_decreases:
				case LITERAL_decreases_redundantly:
				case LITERAL_decreasing:
				case LITERAL_decreasing_redundantly:
				{
					vars=jmlVariantFunctionList();
					break;
				}
				case LITERAL_do:
				case LITERAL_for:
				case LITERAL_while:
				case IDENT:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case LITERAL_decreases:
			case LITERAL_decreases_redundantly:
			case LITERAL_decreasing:
			case LITERAL_decreasing_redundantly:
			{
				vars=jmlVariantFunctionList();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case IDENT:
			{
				stmt=jLabeledStatement();
				if ( inputState.guessing==0 ) {
					
							if (!(((JLabeledStatement)stmt).stmt()
								instanceof JLoopStatement)) {
							    utility.reportTrouble(
								new PositionedError(
								    stmt.getTokenReference(),
								    JmlMessages.LOOP_STMT_EXPECTED));
								}
						
				}
				break;
			}
			case LITERAL_do:
			case LITERAL_for:
			case LITERAL_while:
			{
				stmt=jSimpleLoopStatement();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
					    self = new JmlLoopStatement( sourceRef, invs, vars, stmt, comments );
					
			}
			break;
		}
		case LITERAL_do:
		case LITERAL_for:
		case LITERAL_while:
		{
			self=jSimpleLoopStatement();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlLoopInvariant[]  jmlLoopInvariantList(
		
	) throws RecognitionException, TokenStreamException {
		JmlLoopInvariant[] self = null;
		
		
		JmlLoopInvariant inv = null;
		ArrayList invList = new ArrayList();
		
		
		{
		int _cnt361=0;
		_loop361:
		do {
			if (((LA(1) >= LITERAL_loop_invariant && LA(1) <= LITERAL_maintaining_redundantly))) {
				inv=jmlLoopInvariant();
				if ( inputState.guessing==0 ) {
					invList.add(inv);
				}
			}
			else {
				if ( _cnt361>=1 ) { break _loop361; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt361++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (invList.size() > 0) {
					self = new JmlLoopInvariant[invList.size()];
					invList.toArray( self );
				    }
				    
				
		}
		return self;
	}
	
	public final JmlVariantFunction[]  jmlVariantFunctionList(
		
	) throws RecognitionException, TokenStreamException {
		JmlVariantFunction[] self = null;
		
		
		JmlVariantFunction var = null;
		ArrayList varList = new ArrayList();
		
		
		{
		int _cnt364=0;
		_loop364:
		do {
			if (((LA(1) >= LITERAL_decreases && LA(1) <= LITERAL_decreasing_redundantly))) {
				var=jmlVariantFunction();
				if ( inputState.guessing==0 ) {
					varList.add(var);
				}
			}
			else {
				if ( _cnt364>=1 ) { break _loop364; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt364++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (varList.size() > 0) {
					self = new JmlVariantFunction[varList.size()];
					varList.toArray( self );
				    }
				    
				
		}
		return self;
	}
	
	public final JLabeledStatement  jLabeledStatement(
		
	) throws RecognitionException, TokenStreamException {
		JLabeledStatement self = null;
		
		Token  label = null;
		
		JStatement        stmt;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		label = LT(1);
		match(IDENT);
		match(COLON);
		stmt=jStatement();
		if ( inputState.guessing==0 ) {
			
			if (stmt instanceof JEmptyStatement) {
			utility.reportTrouble(
			new CWarning(sourceRef, 
			MjcMessages.STRAY_SEMICOLON, null));
			}
			self = new JLabeledStatement(sourceRef, label.getText(), stmt, utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JLoopStatement  jSimpleLoopStatement(
		
	) throws RecognitionException, TokenStreamException {
		JLoopStatement self = null;
		
		
		
		
		switch ( LA(1)) {
		case LITERAL_for:
		{
			self=jForStatement();
			break;
		}
		case LITERAL_while:
		{
			self=jWhileStatement();
			break;
		}
		case LITERAL_do:
		{
			self=jDoStatement();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  mjOrJmlUnaryExpressionNotPlusMinus(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op_b = null;
		Token  op_l = null;
		
		long             mods = 0;
		JExpression      expr;
		CType            dest=null;
		TokenReference   sourceRef = utility.buildTokenReference( LT(1) );
		CUniverse        array_univ = null;
		CUniverse        elem_univ = null;
		boolean          isExplicitNonNull = false;
		
		
		switch ( LA(1)) {
		case BNOT:
		{
			op_b = LT(1);
			match(BNOT);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = exprFactory.createUnaryExpression(op_b, self.getTokenReference(), Constants.OPE_BNOT, self);
			}
			break;
		}
		case LNOT:
		{
			op_l = LT(1);
			match(LNOT);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = exprFactory.createUnaryExpression(op_l, self.getTokenReference(), Constants.OPE_LNOT, self);
			}
			break;
		}
		default:
			boolean synPredMatched344 = false;
			if (((LA(1)==LPAREN) && (_tokenSet_26.member(LA(2))))) {
				int _m344 = mark();
				synPredMatched344 = true;
				inputState.guessing++;
				try {
					{
					match(LPAREN);
					{
					switch ( LA(1)) {
					case LITERAL_peer:
					case LITERAL_readonly:
					case LITERAL_rep:
					case LITERAL_U_peer:
					case LITERAL_U_rep:
					case LITERAL_U_readonly:
					{
						jUniverseSpec();
						break;
					}
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_double:
					case LITERAL_float:
					case LITERAL_int:
					case LITERAL_long:
					case LITERAL_short:
					case LITERAL_void:
					case LITERAL_BS_bigint:
					case LITERAL_BS_real:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					jBuiltInTypeSpec(null);
					match(RPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched344 = false;
				}
				rewind(_m344);
inputState.guessing--;
			}
			if ( synPredMatched344 ) {
				match(LPAREN);
				{
				switch ( LA(1)) {
				case LITERAL_peer:
				case LITERAL_readonly:
				case LITERAL_rep:
				case LITERAL_U_peer:
				case LITERAL_U_rep:
				case LITERAL_U_readonly:
				{
					array_univ=jUniverseSpec();
					break;
				}
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_double:
				case LITERAL_float:
				case LITERAL_int:
				case LITERAL_long:
				case LITERAL_short:
				case LITERAL_void:
				case LITERAL_BS_bigint:
				case LITERAL_BS_real:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				dest=jBuiltInTypeSpec(array_univ);
				match(RPAREN);
				expr=jUnaryExpression();
				if ( inputState.guessing==0 ) {
					self = new JCastExpression(sourceRef, expr, dest);
				}
			}
			else {
				boolean synPredMatched348 = false;
				if (((LA(1)==LPAREN) && (LA(2)==IDENT||LA(2)==LITERAL_non_null))) {
					int _m348 = mark();
					synPredMatched348 = true;
					inputState.guessing++;
					try {
						{
						match(LPAREN);
						jmlNonNullNullityModifier();
						{
						switch ( LA(1)) {
						case IDENT:
						{
							jClassTypeSpec(null,null);
							break;
						}
						case RPAREN:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						match(RPAREN);
						jUnaryExpressionNotPlusMinus();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched348 = false;
					}
					rewind(_m348);
inputState.guessing--;
				}
				if ( synPredMatched348 ) {
					match(LPAREN);
					mods=jmlNonNullNullityModifier();
					{
					switch ( LA(1)) {
					case IDENT:
					{
						dest=jClassTypeSpec(elem_univ,array_univ);
						break;
					}
					case RPAREN:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(RPAREN);
					expr=jUnaryExpressionNotPlusMinus();
					if ( inputState.guessing==0 ) {
						boolean isNonNull = (mods == Constants.ACC_NON_NULL);
							  if (isNonNull) {
							     self = new JmlCastExpression(sourceRef, expr, dest, isNonNull); 
							  } else {
							     self = new JCastExpression(sourceRef, expr, dest); 
							  }
							
					}
				}
				else {
					boolean synPredMatched352 = false;
					if (((LA(1)==LPAREN) && (_tokenSet_27.member(LA(2))))) {
						int _m352 = mark();
						synPredMatched352 = true;
						inputState.guessing++;
						try {
							{
							match(LPAREN);
							{
							switch ( LA(1)) {
							case LITERAL_peer:
							case LITERAL_readonly:
							case LITERAL_rep:
							case LITERAL_U_peer:
							case LITERAL_U_rep:
							case LITERAL_U_readonly:
							{
								jUniverseSpec();
								break;
							}
							case IDENT:
							{
								break;
							}
							default:
							{
								throw new NoViableAltException(LT(1), getFilename());
							}
							}
							}
							jClassTypeSpec(null,null);
							match(RPAREN);
							jUnaryExpressionNotPlusMinus();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched352 = false;
						}
						rewind(_m352);
inputState.guessing--;
					}
					if ( synPredMatched352 ) {
						match(LPAREN);
						{
						switch ( LA(1)) {
						case LITERAL_peer:
						case LITERAL_readonly:
						case LITERAL_rep:
						case LITERAL_U_peer:
						case LITERAL_U_rep:
						case LITERAL_U_readonly:
						{
							array_univ=mjUniverseImplicitPeerSpec();
							elem_univ=jUniverseSpec();
							break;
						}
						case IDENT:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						dest=jClassTypeSpec(elem_univ,array_univ);
						match(RPAREN);
						expr=jUnaryExpressionNotPlusMinus();
						if ( inputState.guessing==0 ) {
							self = new JCastExpression(sourceRef, expr, dest);
						}
					}
					else {
						boolean synPredMatched356 = false;
						if (((LA(1)==LPAREN) && (_tokenSet_27.member(LA(2))))) {
							int _m356 = mark();
							synPredMatched356 = true;
							inputState.guessing++;
							try {
								{
								match(LPAREN);
								{
								switch ( LA(1)) {
								case LITERAL_peer:
								case LITERAL_readonly:
								case LITERAL_rep:
								case LITERAL_U_peer:
								case LITERAL_U_rep:
								case LITERAL_U_readonly:
								{
									jUniverseSpec();
									jUniverseSpec();
									break;
								}
								case IDENT:
								{
									break;
								}
								default:
								{
									throw new NoViableAltException(LT(1), getFilename());
								}
								}
								}
								jClassTypeSpec(null,null);
								match(RPAREN);
								jUnaryExpressionNotPlusMinus();
								}
							}
							catch (RecognitionException pe) {
								synPredMatched356 = false;
							}
							rewind(_m356);
inputState.guessing--;
						}
						if ( synPredMatched356 ) {
							match(LPAREN);
							{
							switch ( LA(1)) {
							case LITERAL_peer:
							case LITERAL_readonly:
							case LITERAL_rep:
							case LITERAL_U_peer:
							case LITERAL_U_rep:
							case LITERAL_U_readonly:
							{
								array_univ=jUniverseSpec();
								elem_univ=jUniverseSpec();
								break;
							}
							case IDENT:
							{
								break;
							}
							default:
							{
								throw new NoViableAltException(LT(1), getFilename());
							}
							}
							}
							dest=jClassTypeSpec(elem_univ,array_univ);
							match(RPAREN);
							expr=jUnaryExpressionNotPlusMinus();
							if ( inputState.guessing==0 ) {
								self = new JCastExpression(sourceRef, expr, dest);
							}
						}
						else if ((_tokenSet_28.member(LA(1))) && (_tokenSet_29.member(LA(2)))) {
							self=jPostfixExpression();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}}
					return self;
				}
				
	public final JExpression  jUnaryExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op_m = null;
		Token  op_p = null;
		
		TokenReference    sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case INC:
		{
			match(INC);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = new JPrefixExpression(sourceRef, Constants.OPE_PREINC, self);
			}
			break;
		}
		case DEC:
		{
			match(DEC);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = new JPrefixExpression(sourceRef, Constants.OPE_PREDEC, self);
			}
			break;
		}
		case MINUS:
		{
			op_m = LT(1);
			match(MINUS);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = exprFactory.createUnaryExpression(op_m, self.getTokenReference(), Constants.OPE_MINUS, self);
			}
			break;
		}
		case PLUS:
		{
			op_p = LT(1);
			match(PLUS);
			self=jUnaryExpression();
			if ( inputState.guessing==0 ) {
				self = exprFactory.createUnaryExpression(op_p, self.getTokenReference(), Constants.OPE_PLUS, self);
			}
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case LNOT:
		case LPAREN:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			self=jUnaryExpressionNotPlusMinus();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CUniverse  jUniverseSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		switch ( LA(1)) {
		case LITERAL_peer:
		case LITERAL_U_peer:
		{
			universe=jUniversePeerSpec();
			break;
		}
		case LITERAL_rep:
		case LITERAL_U_rep:
		{
			universe=jUniverseRepSpec();
			break;
		}
		case LITERAL_readonly:
		case LITERAL_U_readonly:
		{
			universe=jUniverseReadonlySpec();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CType  jBuiltInTypeSpec(
		CUniverse array_univ
	) throws RecognitionException, TokenStreamException {
		CType self = null;
		
		
		int            bounds = 0;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		self=jBuiltInType();
		{
		_loop494:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop494;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			if (bounds > 0) {
			self = new CArrayType(self, bounds, array_univ);
			} else {
			// WMD: no universe spec allowed if its just a basic type
			// this gives an error, if the array brackets are after
			// the identifier, e.g. rep int len[] = ... gives an error
			// but this shouldn't restrict usage...
			if( array_univ != null ) {
			utility.reportTrouble(
			new PositionedError(
			sourceRef, 
			CUniverseMessages.BUILTIN_WITH_UNIVERSE_FORBIDDEN, null));
			}
			}
			
		}
		return self;
	}
	
	public final JExpression  jUnaryExpressionNotPlusMinus(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		self=mjOrJmlUnaryExpressionNotPlusMinus();
		return self;
	}
	
	public final CUniverse  mjUniverseImplicitPeerSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		if ( inputState.guessing==0 ) {
			
			// implicit peer reference
			universe = CUniverseImplicitPeer.getUniverse(); 
			
		}
		return universe;
	}
	
	public final JForStatement  jForStatement(
		
	) throws RecognitionException, TokenStreamException {
		JForStatement self = null;
		
		Token  s = null;
		
		JStatement        init;
		JExpression        cond;
		JStatement        iter;        // !FIXME! change type to JExpressionListStatement and propagate
		JStatement        body;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_for);
		match(LPAREN);
		init=jForInit();
		match(SEMI);
		cond=jForCond();
		match(SEMI);
		iter=jForIter();
		match(RPAREN);
		body=jStatement();
		if ( inputState.guessing==0 ) {
			
			if (!(body instanceof JBlock || body instanceof JEmptyStatement)) {
			utility.reportTrouble(
			new CWarning( sourceRef, 
			MjcMessages.ENCLOSE_LOOP_BODY_IN_BLOCK, null));
			}
			self = new JForStatement( sourceRef, init, cond, iter, body, 
			utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JWhileStatement  jWhileStatement(
		
	) throws RecognitionException, TokenStreamException {
		JWhileStatement self = null;
		
		Token  s = null;
		
		JExpression        cond;
		JStatement        body;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_while);
		match(LPAREN);
		cond=jExpression();
		match(RPAREN);
		body=jStatement();
		if ( inputState.guessing==0 ) {
			
			if (!(body instanceof JBlock || body instanceof JEmptyStatement)) {
			utility.reportTrouble(new CWarning(sourceRef, MjcMessages.ENCLOSE_LOOP_BODY_IN_BLOCK, null));
			}
			self = new JWhileStatement(sourceRef, cond, body, utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JDoStatement  jDoStatement(
		
	) throws RecognitionException, TokenStreamException {
		JDoStatement self = null;
		
		Token  s = null;
		
		JExpression        cond;
		JStatement        body;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_do);
		body=jStatement();
		match(LITERAL_while);
		match(LPAREN);
		cond=jExpression();
		match(RPAREN);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			if (! (body instanceof JBlock)) {
			utility.reportTrouble(new CWarning(sourceRef, MjcMessages.ENCLOSE_LOOP_BODY_IN_BLOCK, null));
			}
			self = new JDoStatement(sourceRef, cond, body, utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JmlLoopInvariant  jmlLoopInvariant(
		
	) throws RecognitionException, TokenStreamException {
		JmlLoopInvariant self = null;
		
		
		boolean isRedundantly = false;
		JmlPredicate predicate = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_maintaining:
		{
			match(LITERAL_maintaining);
			break;
		}
		case LITERAL_loop_invariant:
		{
			match(LITERAL_loop_invariant);
			break;
		}
		case LITERAL_loop_invariant_redundantly:
		case LITERAL_maintaining_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_maintaining_redundantly:
			{
				match(LITERAL_maintaining_redundantly);
				break;
			}
			case LITERAL_loop_invariant_redundantly:
			{
				match(LITERAL_loop_invariant_redundantly);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate=jmlPredicate();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlLoopInvariant( sourceRef, isRedundantly, predicate );
				
		}
		return self;
	}
	
	public final JmlVariantFunction  jmlVariantFunction(
		
	) throws RecognitionException, TokenStreamException {
		JmlVariantFunction self = null;
		
		
		boolean isRedundantly = false;
		JmlSpecExpression specExpression = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_decreasing:
		{
			match(LITERAL_decreasing);
			break;
		}
		case LITERAL_decreases:
		{
			match(LITERAL_decreases);
			break;
		}
		case LITERAL_decreases_redundantly:
		case LITERAL_decreasing_redundantly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_decreasing_redundantly:
			{
				match(LITERAL_decreasing_redundantly);
				break;
			}
			case LITERAL_decreases_redundantly:
			{
				match(LITERAL_decreases_redundantly);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		specExpression=jmlSpecExpression();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlVariantFunction( sourceRef, isRedundantly,
					specExpression );
				
		}
		return self;
	}
	
	public final JExpression  jAssignmentExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		int            oper = -1;
		JExpression        right;
		
		
		self=jConditionalExpression();
		{
		switch ( LA(1)) {
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		{
			{
			switch ( LA(1)) {
			case ASSIGN:
			{
				match(ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_SIMPLE;
				}
				break;
			}
			case PLUS_ASSIGN:
			{
				match(PLUS_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_PLUS;
				}
				break;
			}
			case MINUS_ASSIGN:
			{
				match(MINUS_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_MINUS;
				}
				break;
			}
			case STAR_ASSIGN:
			{
				match(STAR_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_STAR;
				}
				break;
			}
			case SLASH_ASSIGN:
			{
				match(SLASH_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_SLASH;
				}
				break;
			}
			case PERCENT_ASSIGN:
			{
				match(PERCENT_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_PERCENT;
				}
				break;
			}
			case SR_ASSIGN:
			{
				match(SR_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_SR;
				}
				break;
			}
			case BSR_ASSIGN:
			{
				match(BSR_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_BSR;
				}
				break;
			}
			case SL_ASSIGN:
			{
				match(SL_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_SL;
				}
				break;
			}
			case BAND_ASSIGN:
			{
				match(BAND_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_BAND;
				}
				break;
			}
			case BXOR_ASSIGN:
			{
				match(BXOR_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_BXOR;
				}
				break;
			}
			case BOR_ASSIGN:
			{
				match(BOR_ASSIGN);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_BOR;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			right=jAssignmentExpression();
			if ( inputState.guessing==0 ) {
				self = JAssignmentExpression.create(self.getTokenReference(), oper, self, right);
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case COLON:
		case COMMA:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case IDENT:
		case DOT_DOT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JmlSpecStatement  jmlSpecStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlSpecStatement self = null;
		
		
		JmlGeneralSpecCase specCase = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JavaStyleComment[] comments = utility.getStatementComment();
		
		
		{
		switch ( LA(1)) {
		case LITERAL_behavior:
		case LITERAL_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_behavior:
			{
				match(LITERAL_behavior);
				break;
			}
			case LITERAL_behaviour:
			{
				match(LITERAL_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlGenericSpecCase(true);
			break;
		}
		case LITERAL_exceptional_behavior:
		case LITERAL_exceptional_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_exceptional_behavior:
			{
				match(LITERAL_exceptional_behavior);
				break;
			}
			case LITERAL_exceptional_behaviour:
			{
				match(LITERAL_exceptional_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlExceptionalSpecCase();
			break;
		}
		case LITERAL_normal_behavior:
		case LITERAL_normal_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_normal_behavior:
			{
				match(LITERAL_normal_behavior);
				break;
			}
			case LITERAL_normal_behaviour:
			{
				match(LITERAL_normal_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlNormalSpecCase();
			break;
		}
		case LITERAL_abrupt_behavior:
		case LITERAL_abrupt_behaviour:
		{
			{
			switch ( LA(1)) {
			case LITERAL_abrupt_behavior:
			{
				match(LITERAL_abrupt_behavior);
				break;
			}
			case LITERAL_abrupt_behaviour:
			{
				match(LITERAL_abrupt_behaviour);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specCase=jmlAbruptSpecCase();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlSpecStatement( sourceRef, specCase, comments );
				
		}
		return self;
	}
	
	public final JmlNondetChoiceStatement  jmlNondeterministicChoice(
		
	) throws RecognitionException, TokenStreamException {
		JmlNondetChoiceStatement self = null;
		
		
		ArrayList stmts = new ArrayList();
		JStatement[] compoundStatement = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LITERAL_choose);
		compoundStatement=jCompoundStatement(null);
		if ( inputState.guessing==0 ) {
			stmts.add( new JBlock( sourceRef, compoundStatement,
					    null ) );
		}
		{
		_loop387:
		do {
			if ((LA(1)==LITERAL_or)) {
				match(LITERAL_or);
				compoundStatement=jCompoundStatement(null);
				if ( inputState.guessing==0 ) {
					stmts.add( new JBlock( sourceRef, compoundStatement,
								null ) );
				}
			}
			else {
				break _loop387;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    JBlock[] alternativeStatements
				    = new JBlock[stmts.size()];
				    stmts.toArray( alternativeStatements );
				    self = new JmlNondetChoiceStatement( sourceRef,
					alternativeStatements,
					utility.getStatementComment() );
				
		}
		return self;
	}
	
	public final JmlNondetIfStatement  jmlNondeterministicIf(
		
	) throws RecognitionException, TokenStreamException {
		JmlNondetIfStatement self = null;
		
		
		JmlGuardedStatement[] guardedStatements = null;
		JStatement[] elseStatements = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LITERAL_choose_if);
		guardedStatements=jmlGuardedStatements();
		{
		if ((LA(1)==LITERAL_else) && (LA(2)==LCURLY)) {
			match(LITERAL_else);
			elseStatements=jCompoundStatement(null);
		}
		else if ((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlNondetIfStatement( sourceRef,
					guardedStatements,
					elseStatements,
					utility.getStatementComment() );
				
		}
		return self;
	}
	
	public final JmlInvariantStatement  jmlInvariantStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlInvariantStatement self = null;
		
		
		boolean isRedundantly = false;
		JmlPredicate predicate;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_invariant:
		{
			match(LITERAL_invariant);
			break;
		}
		case LITERAL_invariant_redundantly:
		{
			match(LITERAL_invariant_redundantly);
			if ( inputState.guessing==0 ) {
				isRedundantly = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate=jmlPredicate();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    self = new JmlInvariantStatement( sourceRef, isRedundantly,
					predicate, utility.getStatementComment() );
				
		}
		return self;
	}
	
	public final JmlGuardedStatement[]  jmlGuardedStatements(
		
	) throws RecognitionException, TokenStreamException {
		JmlGuardedStatement[] self = null;
		
		
		ArrayList stmts = new ArrayList();
		JmlGuardedStatement statement = null;
		
		
		statement=jmlGuardedStatement();
		if ( inputState.guessing==0 ) {
			stmts.add( statement );
		}
		{
		_loop392:
		do {
			if ((LA(1)==LITERAL_or)) {
				match(LITERAL_or);
				statement=jmlGuardedStatement();
				if ( inputState.guessing==0 ) {
					stmts.add( statement );
				}
			}
			else {
				break _loop392;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlGuardedStatement[stmts.size()];
				    stmts.toArray(self);
				
		}
		return self;
	}
	
	public final JmlGuardedStatement  jmlGuardedStatement(
		
	) throws RecognitionException, TokenStreamException {
		JmlGuardedStatement self = null;
		
		
		JmlAssumeStatement assumeStatement;
		JStatement stmt;
		ArrayList stmts = new ArrayList();
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LCURLY);
		assumeStatement=jmlAssumeStatement();
		stmt=jStatement();
		if ( inputState.guessing==0 ) {
			stmts.add( stmt );
		}
		{
		_loop395:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				stmt=jStatement();
				if ( inputState.guessing==0 ) {
					stmts.add( stmt );
				}
			}
			else {
				break _loop395;
			}
			
		} while (true);
		}
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
				    JStatement[] statements = new JStatement[stmts.size()];
				    stmts.toArray(statements);
				    self = new JmlGuardedStatement( sourceRef, assumeStatement,
					statements );
				
		}
		return self;
	}
	
	public final JmlAbruptSpecCase  jmlAbruptSpecCase(
		
	) throws RecognitionException, TokenStreamException {
		 JmlAbruptSpecCase self = null ;
		
		
		JmlSpecVarDecl v[] = null;
		JmlRequiresClause r[] = null;
		JmlAbruptSpecBody b = null;
		TokenReference s = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_forall:
		case LITERAL_old:
		{
			v=jmlSpecVarDecls();
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_pre:
		case LITERAL_pre_redundantly:
		case LITERAL_requires:
		case LITERAL_requires_redundantly:
		{
			{
			r=jmlSpecHeader();
			{
			if ((_tokenSet_16.member(LA(1)))) {
				b=jmlAbruptSpecBody();
			}
			else if ((_tokenSet_32.member(LA(1)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			}
			break;
		}
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		case LCURLY_VBAR:
		{
			b=jmlAbruptSpecBody();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			self = new JmlAbruptSpecCase(s, v, r, b);
			
		}
		return self;
	}
	
	public final JmlAbruptSpecBody  jmlAbruptSpecBody(
		
	) throws RecognitionException, TokenStreamException {
		 JmlAbruptSpecBody self = null ;
		
		
		JmlSpecBodyClause specClauses[] = null;
		JmlGeneralSpecCase specCases[] = null;
		
		
		switch ( LA(1)) {
		case LITERAL_accessible:
		case LITERAL_accessible_redundantly:
		case LITERAL_assignable:
		case LITERAL_assignable_redundantly:
		case LITERAL_breaks:
		case LITERAL_breaks_redundantly:
		case LITERAL_callable:
		case LITERAL_callable_redundantly:
		case LITERAL_captures:
		case LITERAL_captures_redundantly:
		case LITERAL_continues:
		case LITERAL_continues_redundantly:
		case LITERAL_diverges:
		case LITERAL_diverges_redundantly:
		case LITERAL_duration:
		case LITERAL_duration_redundantly:
		case LITERAL_ensures:
		case LITERAL_ensures_redundantly:
		case LITERAL_exsures:
		case LITERAL_exsures_redundantly:
		case LITERAL_measured_by:
		case LITERAL_measured_by_redundantly:
		case LITERAL_modifiable:
		case LITERAL_modifiable_redundantly:
		case LITERAL_modifies:
		case LITERAL_modifies_redundantly:
		case LITERAL_post:
		case LITERAL_post_redundantly:
		case LITERAL_returns:
		case LITERAL_returns_redundantly:
		case LITERAL_signals:
		case LITERAL_signals_only:
		case LITERAL_signals_only_redundantly:
		case LITERAL_signals_redundantly:
		case LITERAL_when:
		case LITERAL_when_redundantly:
		case LITERAL_working_space:
		case LITERAL_working_space_redundantly:
		{
			specClauses=jmlSpecBody();
			if ( inputState.guessing==0 ) {
				
				verifyAbruptSpecBody(specClauses);
				self = new JmlAbruptSpecBody(specClauses);
				
			}
			break;
		}
		case LCURLY_VBAR:
		{
			match(LCURLY_VBAR);
			specCases=jmlAbruptSpecCaseSeq();
			match(VBAR_RCURLY);
			if ( inputState.guessing==0 ) {
				
				self = new JmlAbruptSpecBody(specCases);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JmlGeneralSpecCase[]  jmlAbruptSpecCaseSeq(
		
	) throws RecognitionException, TokenStreamException {
		JmlGeneralSpecCase[] self = null ;
		
		
		ArrayList cases = new ArrayList();
		JmlAbruptSpecCase c1, c2;
		
		
		c1=jmlAbruptSpecCase();
		if ( inputState.guessing==0 ) {
			cases.add(c1);
		}
		{
		_loop410:
		do {
			if ((LA(1)==LITERAL_also)) {
				match(LITERAL_also);
				c2=jmlAbruptSpecCase();
				if ( inputState.guessing==0 ) {
					cases.add(c2);
				}
			}
			else {
				break _loop410;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    self = new JmlGeneralSpecCase[cases.size()];
				    cases.toArray(self);
				    
			//@ assert self.length > 0;
			
		}
		return self;
	}
	
	public final JExpression  jConditionalExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression		middle;
		JExpression		right;
		
		
		self=jmlEquivalenceExpression();
		{
		switch ( LA(1)) {
		case QUESTION:
		{
			match(QUESTION);
			middle=jConditionalExpression();
			match(COLON);
			right=jConditionalExpression();
			if ( inputState.guessing==0 ) {
				self = new JConditionalExpression(self.getTokenReference(), self, middle, right);
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jmlEquivalenceExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression right;
		int oper = -1;
		
		
		self=jmlImpliesExpression();
		{
		switch ( LA(1)) {
		case EQUIV:
		case NOT_EQUIV:
		{
			{
			switch ( LA(1)) {
			case EQUIV:
			{
				match(EQUIV);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_EQUIV;
				}
				break;
			}
			case NOT_EQUIV:
			{
				match(NOT_EQUIV);
				if ( inputState.guessing==0 ) {
					oper = Constants.OPE_NOT_EQUIV;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			right=jmlEquivalenceExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlRelationalExpression( self.getTokenReference(),
						    oper, self, right );
					
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jEqualityExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		int			operator = -1;
		JExpression		right;
		
		
		self=jRelationalExpression();
		{
		_loop418:
		do {
			if ((LA(1)==EQUAL||LA(1)==NOT_EQUAL)) {
				{
				switch ( LA(1)) {
				case NOT_EQUAL:
				{
					match(NOT_EQUAL);
					if ( inputState.guessing==0 ) {
						operator = Constants.OPE_NE;
					}
					break;
				}
				case EQUAL:
				{
					match(EQUAL);
					if ( inputState.guessing==0 ) {
						operator = Constants.OPE_EQ;
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				right=jRelationalExpression();
				if ( inputState.guessing==0 ) {
					self = new JmlEqualityExpression(self.getTokenReference(), operator, self, right);
				}
			}
			else {
				break _loop418;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jRelationalExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		int			operator = -1;
		JExpression		right;
		CType			type;
		
		
		self=jShiftExpression();
		{
		switch ( LA(1)) {
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND:
		case BAND_ASSIGN:
		case BOR:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case EQUAL:
		case GE:
		case GT:
		case LAND:
		case LE:
		case LOR:
		case LT:
		case MINUS_ASSIGN:
		case NOT_EQUAL:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		case IMPLIES:
		case BACKWARD_IMPLIES:
		case EQUIV:
		case NOT_EQUIV:
		{
			{
			_loop423:
			do {
				if ((_tokenSet_33.member(LA(1)))) {
					{
					switch ( LA(1)) {
					case LT:
					{
						match(LT);
						if ( inputState.guessing==0 ) {
							operator = Constants.OPE_LT;
						}
						break;
					}
					case GT:
					{
						match(GT);
						if ( inputState.guessing==0 ) {
							operator = Constants.OPE_GT;
						}
						break;
					}
					case LE:
					{
						match(LE);
						if ( inputState.guessing==0 ) {
							operator = Constants.OPE_LE;
						}
						break;
					}
					case GE:
					{
						match(GE);
						if ( inputState.guessing==0 ) {
							operator = Constants.OPE_GE;
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					right=jShiftExpression();
					if ( inputState.guessing==0 ) {
						self = new JmlRelationalExpression(self.getTokenReference(), operator, self, right);
					}
				}
				else {
					break _loop423;
				}
				
			} while (true);
			}
			break;
		}
		case LITERAL_instanceof:
		{
			match(LITERAL_instanceof);
			type=jTypeSpec();
			if ( inputState.guessing==0 ) {
				self = new JInstanceofExpression(self.getTokenReference(), self, type);
			}
			break;
		}
		case SUBTYPE_OF:
		{
			match(SUBTYPE_OF);
			right=jShiftExpression();
			if ( inputState.guessing==0 ) {
				self = new JmlRelationalExpression(self.getTokenReference(), Constants.OPE_SUBTYPE, self, right);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jShiftExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		int            operator = -1;
		JExpression        right;
		
		
		self=jAdditiveExpression();
		{
		_loop602:
		do {
			if ((_tokenSet_34.member(LA(1)))) {
				{
				switch ( LA(1)) {
				case SL:
				{
					match(SL);
					if ( inputState.guessing==0 ) {
						operator = Constants.OPE_SL;
					}
					break;
				}
				case SR:
				{
					match(SR);
					if ( inputState.guessing==0 ) {
						operator = Constants.OPE_SR;
					}
					break;
				}
				case BSR:
				{
					match(BSR);
					if ( inputState.guessing==0 ) {
						operator = Constants.OPE_BSR;
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				right=jAdditiveExpression();
				if ( inputState.guessing==0 ) {
					self = exprFactory.createShiftExpression(self.getTokenReference(), operator, self, right);
				}
			}
			else {
				break _loop602;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jmlImpliesExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression right;
		
		
		self=jLogicalOrExpression();
		{
		switch ( LA(1)) {
		case IMPLIES:
		{
			match(IMPLIES);
			right=jmlForwardImpliesExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlRelationalExpression( self.getTokenReference(),
						    Constants.OPE_IMPLIES, self, right );
					
			}
			break;
		}
		case BACKWARD_IMPLIES:
		{
			match(BACKWARD_IMPLIES);
			right=jmlBackwardImpliesExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlRelationalExpression( self.getTokenReference(),
						    Constants.OPE_BACKWARD_IMPLIES, self, right );
					
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		case EQUIV:
		case NOT_EQUIV:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jLogicalOrExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression        right;
		
		
		self=jLogicalAndExpression();
		{
		_loop586:
		do {
			if ((LA(1)==LOR)) {
				match(LOR);
				right=jLogicalAndExpression();
				if ( inputState.guessing==0 ) {
					self = new JConditionalOrExpression(self.getTokenReference(), self, right);
				}
			}
			else {
				break _loop586;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jmlForwardImpliesExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression right;
		
		
		self=jLogicalOrExpression();
		{
		switch ( LA(1)) {
		case IMPLIES:
		{
			match(IMPLIES);
			right=jmlForwardImpliesExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlRelationalExpression( self.getTokenReference(),
						    Constants.OPE_IMPLIES, self, right );
					
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		case EQUIV:
		case NOT_EQUIV:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jmlBackwardImpliesExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression right;
		
		
		self=jLogicalOrExpression();
		{
		switch ( LA(1)) {
		case BACKWARD_IMPLIES:
		{
			match(BACKWARD_IMPLIES);
			right=jmlBackwardImpliesExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlRelationalExpression( self.getTokenReference(),
						    Constants.OPE_BACKWARD_IMPLIES, self, right );
					
			}
			break;
		}
		case LITERAL_for:
		case LITERAL_if:
		case ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BSR_ASSIGN:
		case BXOR_ASSIGN:
		case COLON:
		case COMMA:
		case MINUS_ASSIGN:
		case PERCENT_ASSIGN:
		case PLUS_ASSIGN:
		case QUESTION:
		case RBRACK:
		case RCURLY:
		case RPAREN:
		case SEMI:
		case SLASH_ASSIGN:
		case SL_ASSIGN:
		case SR_ASSIGN:
		case STAR_ASSIGN:
		case IDENT:
		case DOT_DOT:
		case EQUIV:
		case NOT_EQUIV:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jPrimaryExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case LPAREN:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		{
			self=mjPrimaryExpression();
			break;
		}
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case INFORMAL_DESC:
		{
			self=jmlPrimary();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  mjPrimaryExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  ident = null;
		Token  id = null;
		Token  l = null;
		Token  d = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JExpression[] args = null;
		JExpression expr = null;
		CType type;
		CUniverse univ = null;
		int bounds = 0;
		
		
		switch ( LA(1)) {
		case LPAREN:
		{
			self=jParenthesizedExpression();
			break;
		}
		case LITERAL_this:
		{
			match(LITERAL_this);
			if ( inputState.guessing==0 ) {
				self = new JThisExpression(sourceRef);
			}
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				args=jArgList();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					self = new JExplicitConstructorInvocation(
					utility.buildTokenReference(),
					((JThisExpression) self).prefix(), 
					Constants.JAV_THIS, args);
					
				}
				break;
			}
			case LITERAL_for:
			case LITERAL_if:
			case LITERAL_instanceof:
			case ASSIGN:
			case BAND:
			case BAND_ASSIGN:
			case BOR:
			case BOR_ASSIGN:
			case BSR:
			case BSR_ASSIGN:
			case BXOR:
			case BXOR_ASSIGN:
			case COLON:
			case COMMA:
			case DEC:
			case DOT:
			case EQUAL:
			case GE:
			case GT:
			case INC:
			case LAND:
			case LBRACK:
			case LE:
			case LOR:
			case LT:
			case MINUS:
			case MINUS_ASSIGN:
			case NOT_EQUAL:
			case PERCENT:
			case PERCENT_ASSIGN:
			case PLUS:
			case PLUS_ASSIGN:
			case QUESTION:
			case RBRACK:
			case RCURLY:
			case RPAREN:
			case SEMI:
			case SL:
			case SLASH:
			case SLASH_ASSIGN:
			case SL_ASSIGN:
			case SR:
			case SR_ASSIGN:
			case STAR:
			case STAR_ASSIGN:
			case IDENT:
			case DOT_DOT:
			case IMPLIES:
			case BACKWARD_IMPLIES:
			case EQUIV:
			case NOT_EQUIV:
			case SUBTYPE_OF:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_super:
		{
			match(LITERAL_super);
			self=jSuperSuffix( new JSuperExpression(sourceRef) );
			break;
		}
		case CHARACTER_LITERAL:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		{
			self=jConstant();
			break;
		}
		case LITERAL_true:
		{
			match(LITERAL_true);
			if ( inputState.guessing==0 ) {
				self = new JBooleanLiteral(sourceRef, true);
			}
			break;
		}
		case LITERAL_false:
		{
			match(LITERAL_false);
			if ( inputState.guessing==0 ) {
				self = new JBooleanLiteral(sourceRef, false);
			}
			break;
		}
		case LITERAL_null:
		{
			match(LITERAL_null);
			if ( inputState.guessing==0 ) {
				self = new JNullLiteral(sourceRef);
			}
			break;
		}
		case LITERAL_new:
		{
			self=jNewExpression(null);
			break;
		}
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case IDENT:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		{
			{
			switch ( LA(1)) {
			case LITERAL_peer:
			case LITERAL_readonly:
			case LITERAL_rep:
			case LITERAL_U_peer:
			case LITERAL_U_rep:
			case LITERAL_U_readonly:
			{
				univ=jUniverseSpec();
				break;
			}
			case IDENT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			ident = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				self = new JNameExpression(sourceRef, ident.getText(), univ);
			}
			{
			_loop623:
			do {
				if ((LA(1)==DOT) && (LA(2)==IDENT)) {
					match(DOT);
					id = LT(1);
					match(IDENT);
					if ( inputState.guessing==0 ) {
						self = new JNameExpression(utility.buildTokenReference(), self, 
						id.getText(), univ );
					}
				}
				else {
					break _loop623;
				}
				
			} while (true);
			}
			{
			boolean synPredMatched626 = false;
			if (((LA(1)==LBRACK) && (LA(2)==RBRACK))) {
				int _m626 = mark();
				synPredMatched626 = true;
				inputState.guessing++;
				try {
					{
					match(LBRACK);
					match(RBRACK);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched626 = false;
				}
				rewind(_m626);
inputState.guessing--;
			}
			if ( synPredMatched626 ) {
				{
				int _cnt628=0;
				_loop628:
				do {
					if ((LA(1)==LBRACK)) {
						match(LBRACK);
						match(RBRACK);
						if ( inputState.guessing==0 ) {
							bounds++;
						}
					}
					else {
						if ( _cnt628>=1 ) { break _loop628; } else {throw new NoViableAltException(LT(1), getFilename());}
					}
					
					_cnt628++;
				} while (true);
				}
				match(DOT);
				match(LITERAL_class);
				if ( inputState.guessing==0 ) {
					self = new JClassExpression(utility.buildTokenReference(), 
					self, bounds);
					
				}
			}
			else {
				boolean synPredMatched630 = false;
				if (((LA(1)==DOT) && (LA(2)==LITERAL_class))) {
					int _m630 = mark();
					synPredMatched630 = true;
					inputState.guessing++;
					try {
						{
						match(DOT);
						match(LITERAL_class);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched630 = false;
					}
					rewind(_m630);
inputState.guessing--;
				}
				if ( synPredMatched630 ) {
					match(DOT);
					match(LITERAL_class);
					if ( inputState.guessing==0 ) {
						self = new JClassExpression(utility.buildTokenReference(), 
						self, 0);
						
					}
				}
				else if ((LA(1)==LPAREN)) {
					l = LT(1);
					match(LPAREN);
					args=jArgList();
					match(RPAREN);
					if ( inputState.guessing==0 ) {
						self = new JMethodCallExpression(utility.buildTokenReference(), 
						self, args); 
						
					}
				}
				else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_36.member(LA(2)))) {
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_double:
			case LITERAL_float:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_short:
			case LITERAL_void:
			case LITERAL_BS_bigint:
			case LITERAL_BS_real:
			{
				type=jBuiltInType();
				{
				_loop632:
				do {
					if ((LA(1)==LBRACK)) {
						match(LBRACK);
						match(RBRACK);
						if ( inputState.guessing==0 ) {
							bounds++;
						}
					}
					else {
						break _loop632;
					}
					
				} while (true);
				}
				d = LT(1);
				match(DOT);
				match(LITERAL_class);
				if ( inputState.guessing==0 ) {
					
					if (bounds > 0 && type == CStdType.Void) {
					throw new NoViableAltException(d, getFilename());
					}
					type = bounds > 0 ? new CArrayType(type, bounds, null) : type;
					self = new JClassExpression(utility.buildTokenReference(), type);
					
				}
				break;
			}
			case LITERAL_resend:
			{
				match(LITERAL_resend);
				self=mjResendSuffix(null);
				break;
			}
			case LITERAL__warn:
			case LITERAL__warn_op:
			case LITERAL__nowarn:
			case LITERAL__nowarn_op:
			{
				self=mjWarnExpression();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			return self;
		}
		
	public final JExpression  jParenthesizedExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		boolean isPosLabel = false;
		JmlSpecExpression specExpression;
		
		
		match(LPAREN);
		self=jParenthesizedExpressionRest(sourceRef);
		return self;
	}
	
	public final JExpression  jParenthesizedExpressionRest(
		TokenReference sourceRef
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  lblIdent = null;
		
		boolean isPosLabel = false;
		JmlSpecExpression specExpression;
		
		
		{
		if (((_tokenSet_24.member(LA(1))) && (_tokenSet_37.member(LA(2))))&&( LA(1) != LITERAL_BS_max  || LA(2) == LPAREN )) {
			self=jAssignmentExpression();
			if ( inputState.guessing==0 ) {
				self = new JParenthesedExpression( sourceRef, self );
			}
		}
		else if ((LA(1)==LITERAL_BS_lblneg||LA(1)==LITERAL_BS_lblpos)) {
			{
			switch ( LA(1)) {
			case LITERAL_BS_lblneg:
			{
				match(LITERAL_BS_lblneg);
				break;
			}
			case LITERAL_BS_lblpos:
			{
				match(LITERAL_BS_lblpos);
				if ( inputState.guessing==0 ) {
					isPosLabel = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			lblIdent = LT(1);
			match(IDENT);
			specExpression=jmlSpecExpression();
			if ( inputState.guessing==0 ) {
				
						self = new JmlLabelExpression( sourceRef, isPosLabel,
						    lblIdent.getText(), specExpression );
					
			}
		}
		else if (((_tokenSet_38.member(LA(1))) && (_tokenSet_39.member(LA(2))))&&( LA(1) != LITERAL_BS_max  || LA(2) != LPAREN )) {
			self=jmlSpecQuantifiedExprRest(sourceRef);
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		match(RPAREN);
		return self;
	}
	
	public final JExpression  jNewExpression(
		JExpression expr
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		CType			type;
		JExpression[]		args;
		JArrayInitializer	init = null;
		JClassDeclarationType	decl = null;
		CParseClassContext	context = null;
		CUniverse             array_univ = null;
		CUniverse             elem_univ = null;
		long                  mods = 0;
		
		
		match(LITERAL_new);
		{
		boolean synPredMatched443 = false;
		if (((_tokenSet_3.member(LA(1))) && (_tokenSet_3.member(LA(2))))) {
			int _m443 = mark();
			synPredMatched443 = true;
			inputState.guessing++;
			try {
				{
				jUniverseType();
				jUniverseSpec();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched443 = false;
			}
			rewind(_m443);
inputState.guessing--;
		}
		if ( synPredMatched443 ) {
			array_univ=jUniverseType();
			elem_univ=jUniverseSpec();
		}
		else if ((_tokenSet_3.member(LA(1))) && (_tokenSet_40.member(LA(2)))) {
			elem_univ=jUniverseType();
		}
		else if ((_tokenSet_40.member(LA(1)))) {
			if ( inputState.guessing==0 ) {
				/* nothing */
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		{
		if ((_tokenSet_20.member(LA(1))) && (_tokenSet_41.member(LA(2)))) {
			mods=jmlNullityModifier();
		}
		else if ((_tokenSet_41.member(LA(1))) && (_tokenSet_42.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		type=jType(elem_univ);
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			match(LPAREN);
			args=jArgList();
			match(RPAREN);
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				if ( inputState.guessing==0 ) {
					context = getParseClassContext();
				}
				if ( inputState.guessing==0 ) {
					// WMD: TODO anonymous classes can't have a universe right now
					if( array_univ != null || elem_univ != null ) {
					// report error if there was a universe specified
					utility.reportTrouble(
					new PositionedError(
					utility.buildTokenReference(), 
					CUniverseMessages.ANON_CLASS_WITH_UNIVERSE_FORBIDDEN, null));
					}
					if( mods !=0 ) {
					// report error if there was a nullity specified
					utility.reportTrouble(
					new PositionedError(
					utility.buildTokenReference(), 
					JmlMessages.UNEXPECTED_NULLITY_ANNOTATION, null));
					}
					
				}
				jClassBlock(context);
				if ( inputState.guessing==0 ) {
					
							    decl = new JClassDeclarationWrapper(
								utility.buildTokenReference(), 0,
					//(CClassType)type,
					((CClassType)type).qualifiedName(), // !!!
								null, CClassType.EMPTY, context.getMethods(),
								context.getInnerClasses(), context.getFieldsAndInits(),
								null,	// no javadoc comments on anonymous classes
								utility.getStatementComment() );
							    context.release();
							
				}
				if ( inputState.guessing==0 ) {
					
							    self = new JNewAnonymousClassExpression(
								utility.buildTokenReference(),
								(CClassType)type, expr, args, decl
							    );
							
				}
				break;
			}
			case LITERAL_for:
			case LITERAL_if:
			case LITERAL_instanceof:
			case ASSIGN:
			case BAND:
			case BAND_ASSIGN:
			case BOR:
			case BOR_ASSIGN:
			case BSR:
			case BSR_ASSIGN:
			case BXOR:
			case BXOR_ASSIGN:
			case COLON:
			case COMMA:
			case DEC:
			case DOT:
			case EQUAL:
			case GE:
			case GT:
			case INC:
			case LAND:
			case LBRACK:
			case LE:
			case LOR:
			case LT:
			case MINUS:
			case MINUS_ASSIGN:
			case NOT_EQUAL:
			case PERCENT:
			case PERCENT_ASSIGN:
			case PLUS:
			case PLUS_ASSIGN:
			case QUESTION:
			case RBRACK:
			case RCURLY:
			case RPAREN:
			case SEMI:
			case SL:
			case SLASH:
			case SLASH_ASSIGN:
			case SL_ASSIGN:
			case SR:
			case SR_ASSIGN:
			case STAR:
			case STAR_ASSIGN:
			case IDENT:
			case DOT_DOT:
			case IMPLIES:
			case BACKWARD_IMPLIES:
			case EQUIV:
			case NOT_EQUIV:
			case SUBTYPE_OF:
			{
				if ( inputState.guessing==0 ) {
					
					// WMD some error checking
					if( array_univ != null && elem_univ != null ) {
					// report error if there was an array universe specified
					utility.reportTrouble(
					new PositionedError(
					utility.buildTokenReference(), 
					CUniverseMessages.NONARRAY_WITH_TWO_UNIVERSES_FORBIDDEN, null));
					}
					if( mods !=0 ) {
					// report error if there was a nullity specified
					utility.reportTrouble(
					new PositionedError(
					utility.buildTokenReference(), 
					JmlMessages.UNEXPECTED_NULLITY_ANNOTATION, null));
					}
					
							    self = new JNewObjectExpression(
								utility.buildTokenReference(),
								(CClassType)type, expr, args );
							
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LBRACK:
		{
			args=jNewArrayDeclarator();
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				init=jArrayInitializer();
				break;
			}
			case LITERAL_for:
			case LITERAL_if:
			case LITERAL_instanceof:
			case ASSIGN:
			case BAND:
			case BAND_ASSIGN:
			case BOR:
			case BOR_ASSIGN:
			case BSR:
			case BSR_ASSIGN:
			case BXOR:
			case BXOR_ASSIGN:
			case COLON:
			case COMMA:
			case DEC:
			case DOT:
			case EQUAL:
			case GE:
			case GT:
			case INC:
			case LAND:
			case LBRACK:
			case LE:
			case LOR:
			case LT:
			case MINUS:
			case MINUS_ASSIGN:
			case NOT_EQUAL:
			case PERCENT:
			case PERCENT_ASSIGN:
			case PLUS:
			case PLUS_ASSIGN:
			case QUESTION:
			case RBRACK:
			case RCURLY:
			case RPAREN:
			case SEMI:
			case SL:
			case SLASH:
			case SLASH_ASSIGN:
			case SL_ASSIGN:
			case SR:
			case SR_ASSIGN:
			case STAR:
			case STAR_ASSIGN:
			case IDENT:
			case DOT_DOT:
			case IMPLIES:
			case BACKWARD_IMPLIES:
			case EQUIV:
			case NOT_EQUIV:
			case SUBTYPE_OF:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				
				// WMD distinction between a class type and a builtin
				if( type instanceof CClassType ) {
				
				if( elem_univ != null &&
				(elem_univ instanceof CUniverseRep) ) {
				utility.reportTrouble(
				new PositionedError( utility.buildTokenReference(), 
				CUniverseMessages.ARRAY_WITH_REP_ELEM_FORBIDDEN,
				null));
				}
				
				self = new JNewArrayExpression(
				utility.buildTokenReference(), type,
				(mods == 0 ?
				new   JArrayDimsAndInits( utility.buildTokenReference(), array_univ, args, init) :
				new JmlArrayDimsAndInits( utility.buildTokenReference(), array_univ, args, init, mods)));
				} else {
				// WMD: the element is a builtin type
				
				if( array_univ != null ) {
				// report error if there were two universes specified
				utility.reportTrouble(
				new PositionedError( utility.buildTokenReference(), 
				CUniverseMessages.BUILTIN_WITH_UNIVERSE_FORBIDDEN,
				null));
				}
				
				// use the elem_univ for the whole array
				self = new JNewArrayExpression(
				utility.buildTokenReference(), type,
				(mods == 0 ?
				new   JArrayDimsAndInits( utility.buildTokenReference(), elem_univ, args, init) :
				new JmlArrayDimsAndInits( utility.buildTokenReference(), elem_univ, args, init, mods)));
				}
				
			}
			break;
		}
		case LCURLY:
		{
			self=jmlSetComprehension(type);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final CType  jType(
		CUniverse elem_univ
	) throws RecognitionException, TokenStreamException {
		CType type = null;
		
		
		String    name;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_short:
		case LITERAL_void:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		{
			type=jBuiltInType();
			break;
		}
		case IDENT:
		{
			type=jTypeName(elem_univ);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return type;
	}
	
	public final JExpression[]  jArgList(
		
	) throws RecognitionException, TokenStreamException {
		JExpression[] self = JExpression.EMPTY;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			self=jExpressionList();
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression[]  jNewArrayDeclarator(
		
	) throws RecognitionException, TokenStreamException {
		JExpression[] self = null;
		
		
		boolean        unspec = false;
		ArrayList        vect = new ArrayList();
		JExpression        exp  = null;
		
		
		{
		int _cnt642=0;
		_loop642:
		do {
			if ((LA(1)==LBRACK) && (_tokenSet_43.member(LA(2)))) {
				match(LBRACK);
				{
				if (((_tokenSet_24.member(LA(1))))&&( !unspec )) {
					exp=jExpression();
				}
				else if ((LA(1)==RBRACK)) {
					if ( inputState.guessing==0 ) {
						unspec = true;
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					vect.add(exp); exp = null;
				}
			}
			else {
				if ( _cnt642>=1 ) { break _loop642; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt642++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new JExpression[vect.size()];
			self = (JExpression[]) vect.toArray(self);
			
			
		}
		return self;
	}
	
	public final JArrayInitializer  jArrayInitializer(
		
	) throws RecognitionException, TokenStreamException {
		JArrayInitializer self = null;
		
		Token  s = null;
		
		JExpression        expr = null;
		ArrayList        vect = new ArrayList();
		TokenReference    sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LCURLY);
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LCURLY:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			expr=jInitializer();
			if ( inputState.guessing==0 ) {
				vect.add(expr);
			}
			{
			_loop523:
			do {
				if ((LA(1)==COMMA) && (_tokenSet_21.member(LA(2)))) {
					match(COMMA);
					expr=jInitializer();
					if ( inputState.guessing==0 ) {
						vect.add(expr);
					}
				}
				else {
					break _loop523;
				}
				
			} while (true);
			}
			break;
		}
		case COMMA:
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case COMMA:
		{
			match(COMMA);
			if ( inputState.guessing==0 ) {
				
				utility.reportTrouble(
				new CWarning(sourceRef, 
				MjcMessages.STRAY_COMMA, null)); 
				
			}
			break;
		}
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
			self = new JArrayInitializer(sourceRef, 
			(JExpression[]) vect.toArray(new JExpression[0])); 
			
			
		}
		return self;
	}
	
	public final String  jIdentifier(
		
	) throws RecognitionException, TokenStreamException {
		String self = null;
		
		Token  i = null;
		Token  j = null;
		
		StringBuffer buffer = null;
		
		
		i = LT(1);
		match(IDENT);
		{
		_loop507:
		do {
			if ((LA(1)==DOT)) {
				match(DOT);
				j = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					
					(buffer == null 
					? (buffer = new StringBuffer(i.getText())) : buffer)
					.append('/').append(j.getText());
				}
			}
			else {
				break _loop507;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = buffer == null ? i.getText() : buffer.toString(); 
			
		}
		return self;
	}
	
	public final void jTypeDefinition(
		CParseCompilationUnitContext context,
    long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		
		Token  s = null;
		
		JTypeDeclarationType    decl = null;
		TokenReference sourceRef = utility.buildTokenReference( startToken );
		
		
		switch ( LA(1)) {
		case LITERAL_class:
		case LITERAL_interface:
		{
			{
			switch ( LA(1)) {
			case LITERAL_class:
			{
				decl=jClassDefinition(mods,startToken);
				break;
			}
			case LITERAL_interface:
			{
				decl=jInterfaceDefinition(mods,startToken);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				context.addTypeDeclaration( utility.getCompiler(), decl );
			}
			break;
		}
		case SEMI:
		{
			s = LT(1);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
				utility.reportTrouble(
				new CWarning( sourceRef,
				MjcMessages.STRAY_SEMICOLON, null )); 
				utility.flushJavadocTokensWithWarning( s );
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void mjTopLevelDeclaration(
		CParseCompilationUnitContext context, 
    long mods, Token startToken
	) throws RecognitionException, TokenStreamException {
		
		
		MJTopLevelMethodDeclaration    mDecl = null;
		
		
		mDecl=mjTopLevelMethodDeclaration(mods, startToken);
		if ( inputState.guessing==0 ) {
			context.addMJTopLevelMethodDeclaration(utility.getCompiler(), mDecl);
		}
	}
	
	public final CClassType  jWildCard(
		
	) throws RecognitionException, TokenStreamException {
		CClassType self = null;
		
		
		CClassType bound = null;
		
		
		if ((LA(1)==QUESTION) && (LA(2)==COMMA||LA(2)==GT)) {
			match(QUESTION);
			if ( inputState.guessing==0 ) {
				
				self = CWildcardType.createWildcard();
				
			}
		}
		else if ((LA(1)==QUESTION) && (LA(2)==LITERAL_extends)) {
			match(QUESTION);
			match(LITERAL_extends);
			bound=jWildcardBound();
			if ( inputState.guessing==0 ) {
				
					    self = CWildcardType.createUpperBoundedWildcard(bound);
				
			}
		}
		else if ((LA(1)==QUESTION) && (LA(2)==LITERAL_super)) {
			match(QUESTION);
			match(LITERAL_super);
			bound=jWildcardBound();
			if ( inputState.guessing==0 ) {
				
					    self = CWildcardType.createLowerBoundedWildcard(bound);
				
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		return self;
	}
	
	public final CClassType  jWildcardBound(
		
	) throws RecognitionException, TokenStreamException {
		CClassType self = null;
		
		
		int bounds = 0;
		CType type;
		
		
		switch ( LA(1)) {
		case IDENT:
		{
			self=jClassTypeSpec(null, null);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_short:
		case LITERAL_void:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		{
			type=jBuiltInType();
			{
			int _cnt461=0;
			_loop461:
			do {
				if ((LA(1)==LBRACK)) {
					match(LBRACK);
					match(RBRACK);
					if ( inputState.guessing==0 ) {
						bounds += 1;
					}
				}
				else {
					if ( _cnt461>=1 ) { break _loop461; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt461++;
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				self = new CArrayType(type, bounds, null);
				
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CClassType[]  jParameterizedClassTypeList(
		
	) throws RecognitionException, TokenStreamException {
		CClassType[] self = null;
		
		
		CType typeParameter =null;
		ArrayList vect = new ArrayList();
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		match(LT);
		if ( inputState.guessing==0 ) {
			utility.setUnmatchedTypeLT(unmatchedTypeLT++);
		}
		typeParameter=jTypeParameter();
		if ( inputState.guessing==0 ) {
			vect.add(typeParameter);
		}
		{
		_loop475:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				typeParameter=jTypeParameter();
				if ( inputState.guessing==0 ) {
					vect.add(typeParameter);
				}
			}
			else {
				break _loop475;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self =(CClassType[])vect.toArray(new CClassType[vect.size()]);
			
		}
		match(GT);
		if ( inputState.guessing==0 ) {
			utility.setUnmatchedTypeLT(unmatchedTypeLT--);
		}
		if ( inputState.guessing==0 ) {
			
			if (!utility.allowGeneric) {
			utility.reportTrouble(new PositionedError(sourceRef,MjcMessages.UNSUPPORTED_GENERIC_TYPE,null));
			}        
			
		}
		return self;
	}
	
	public final CClassType  jTypeParameter(
		
	) throws RecognitionException, TokenStreamException {
		CClassType self = null;
		
		
		int bounds = 0;
		CType type;
		
		
		switch ( LA(1)) {
		case IDENT:
		{
			self=jClassTypeSpec(null, null);
			break;
		}
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_short:
		case LITERAL_void:
		case LITERAL_BS_bigint:
		case LITERAL_BS_real:
		{
			type=jBuiltInType();
			{
			int _cnt472=0;
			_loop472:
			do {
				if ((LA(1)==LBRACK)) {
					match(LBRACK);
					match(RBRACK);
					if ( inputState.guessing==0 ) {
						bounds += 1;
					}
				}
				else {
					if ( _cnt472>=1 ) { break _loop472; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt472++;
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				self = new CArrayType(type, bounds, null);
				
			}
			break;
		}
		case QUESTION:
		{
			self=jWildCard();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final CTypeVariable  jTypeVariableDeclaration(
		
	) throws RecognitionException, TokenStreamException {
		CTypeVariable self = null;
		
		Token  ident = null;
		
		String name = null;
		CClassType     bound = null;
		ArrayList vect = new ArrayList();
		
		
		ident = LT(1);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			match(LITERAL_extends);
			bound=jTypeName(null);
			if ( inputState.guessing==0 ) {
				vect.add(bound) ;
			}
			{
			_loop484:
			do {
				if ((LA(1)==BAND)) {
					match(BAND);
					bound=jTypeName(null);
					if ( inputState.guessing==0 ) {
						vect.add(bound);
					}
				}
				else {
					break _loop484;
				}
				
			} while (true);
			}
			break;
		}
		case COMMA:
		case GT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			self = new CTypeVariable(ident.getText(), 
			(CClassType[])vect.toArray(new CClassType[vect.size()]));
			
		}
		return self;
	}
	
	public final CUniverse  jUniverseExceptionSpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case EOF:
		{
			universe=mjUniverseImplicitReadonlySpec();
			break;
		}
		case LITERAL_readonly:
		case LITERAL_U_readonly:
		{
			universe=jUniverseReadonlySpec();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return universe;
	}
	
	public final CUniverse  mjUniverseImplicitReadonlySpec(
		
	) throws RecognitionException, TokenStreamException {
		CUniverse universe = null;
		
		
		if ( inputState.guessing==0 ) {
			
			universe = CUniverseImplicitReadonly.getUniverse();
			
		}
		return universe;
	}
	
	public final JVariableDefinition  jVariableDeclarator(
		long mods, CType type
	) throws RecognitionException, TokenStreamException {
		JVariableDefinition self = null;
		
		Token  ident = null;
		
		int            bounds = 0;
		JExpression        expr = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		ident = LT(1);
		match(IDENT);
		{
		_loop517:
		do {
			if ((LA(1)==LBRACK)) {
				match(LBRACK);
				match(RBRACK);
				if ( inputState.guessing==0 ) {
					bounds += 1;
				}
			}
			else {
				break _loop517;
			}
			
		} while (true);
		}
		expr=jVarInitializer();
		if ( inputState.guessing==0 ) {
			
			if (bounds > 0) {
			if( utility.getCompiler().universeChecks() ) {
			utility.reportTrouble(new CWarning(sourceRef, 
			CUniverseMessages.OLD_STYLE_ARRAY_BOUNDS, 
			null));
			} else {
			utility.reportTrouble(new CWarning(sourceRef, MjcMessages.OLD_STYLE_ARRAY_BOUNDS, null));
			}
			type = new CArrayType(type, bounds, null);
			}
			self = new JVariableDefinition(sourceRef, mods, type, ident.getText(), expr);
			
		}
		return self;
	}
	
	public final JExpression  jVarInitializer(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		{
		switch ( LA(1)) {
		case ASSIGN:
		{
			match(ASSIGN);
			self=jInitializer();
			break;
		}
		case COMMA:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression  jInitializer(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			self=jExpression();
			break;
		}
		case LCURLY:
		{
			self=jArrayInitializer();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JIfStatement  jIfStatement(
		
	) throws RecognitionException, TokenStreamException {
		JIfStatement self = null;
		
		Token  s = null;
		
		JExpression        cond;
		JStatement        thenClause;
		JStatement        elseClause = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_if);
		match(LPAREN);
		cond=jExpression();
		match(RPAREN);
		thenClause=jStatement();
		{
		if ((LA(1)==LITERAL_else) && (_tokenSet_8.member(LA(2)))) {
			match(LITERAL_else);
			elseClause=jStatement();
		}
		else if ((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		if ( inputState.guessing==0 ) {
			
			if (! (thenClause instanceof JBlock)) {
			utility.reportTrouble(new CWarning(sourceRef, MjcMessages.ENCLOSE_IF_THEN_IN_BLOCK, null));
			}
			if (elseClause != null && !(elseClause instanceof JBlock || elseClause instanceof JIfStatement)) {
			utility.reportTrouble(new CWarning(sourceRef, MjcMessages.ENCLOSE_IF_ELSE_IN_BLOCK, null));
			}
			self = new JIfStatement(sourceRef, cond, thenClause, elseClause, utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JBreakStatement  jBreakStatement(
		
	) throws RecognitionException, TokenStreamException {
		JBreakStatement self = null;
		
		Token  s = null;
		Token  label = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_break);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			label = LT(1);
			match(IDENT);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JBreakStatement(sourceRef, 
			label == null ? null : label.getText(), 
			utility.getStatementComment()); 
			
		}
		return self;
	}
	
	public final JContinueStatement  jContinueStatement(
		
	) throws RecognitionException, TokenStreamException {
		JContinueStatement self = null;
		
		Token  s = null;
		Token  label = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_continue);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			label = LT(1);
			match(IDENT);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JContinueStatement(sourceRef, 
			label == null ? null : label.getText(), 
			utility.getStatementComment()); 
			
		}
		return self;
	}
	
	public final JReturnStatement  jReturnStatement(
		
	) throws RecognitionException, TokenStreamException {
		JReturnStatement self = null;
		
		Token  s = null;
		
		JExpression        expr = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_return);
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			expr=jExpression();
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JReturnStatement(sourceRef, expr, 
			utility.getStatementComment()); 
			
		}
		return self;
	}
	
	public final JSwitchStatement  jSwitchStatement(
		
	) throws RecognitionException, TokenStreamException {
		JSwitchStatement self = null;
		
		Token  s = null;
		
		JExpression        expr = null;
		ArrayList        body = null;
		JSwitchGroup        group;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_switch);
		match(LPAREN);
		expr=jExpression();
		match(RPAREN);
		match(LCURLY);
		if ( inputState.guessing==0 ) {
			
			body = new ArrayList(); 
			
		}
		{
		_loop555:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default)) {
				group=jCasesGroup();
				if ( inputState.guessing==0 ) {
					body.add(group);
				}
			}
			else {
				break _loop555;
			}
			
		} while (true);
		}
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			
			self = new JSwitchStatement(sourceRef,
			expr, 
			(JSwitchGroup[]) body.toArray( new JSwitchGroup[0] ),
			utility.getStatementComment());
			
			
		}
		return self;
	}
	
	public final JStatement  jTryBlock(
		
	) throws RecognitionException, TokenStreamException {
		JStatement self = null;
		
		Token  s = null;
		
		JBlock        tryClause = null;
		JStatement[]        compound;
		ArrayList        catchClauses = new ArrayList();
		JBlock        finallyClause = null;
		JCatchClause        catcher = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_try);
		compound=jCompoundStatement(null);
		if ( inputState.guessing==0 ) {
			
			tryClause = new JBlock(sourceRef, compound, null); 
			
		}
		{
		_loop574:
		do {
			if ((LA(1)==LITERAL_catch)) {
				catcher=jHandler();
				if ( inputState.guessing==0 ) {
					catchClauses.add(catcher);
				}
			}
			else {
				break _loop574;
			}
			
		} while (true);
		}
		{
		if ((LA(1)==LITERAL_finally)) {
			match(LITERAL_finally);
			compound=jCompoundStatement(null);
			if ( inputState.guessing==0 ) {
				finallyClause = new JBlock(sourceRef, compound, null);
			}
		}
		else if ((_tokenSet_30.member(LA(1)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		if ( inputState.guessing==0 ) {
			
			if (catchClauses.size() > 0) {
			self = new JTryCatchStatement(sourceRef,
			tryClause,
			(JCatchClause[]) catchClauses.toArray(new JCatchClause[0] ),
			finallyClause == null ? utility.getStatementComment() : null);
			
			}
			if (finallyClause != null) {
			// If both catch and finally clauses are present,
			// the try-catch is embedded as try clause into a
			// try-finally statement.
			if (self != null) {
			tryClause = new JBlock(sourceRef, new JStatement[] {self}, null);
			}
			self = new JTryFinallyStatement(sourceRef, tryClause, finallyClause, utility.getStatementComment());
			}
			
			if (self == null) {
			// try without catch or finally: error
			utility.reportTrouble(new PositionedError(sourceRef, MjcMessages.TRY_NOCATCH, null));
			self = tryClause;
			}
			
		}
		return self;
	}
	
	public final JThrowStatement  jThrowStatement(
		
	) throws RecognitionException, TokenStreamException {
		JThrowStatement self = null;
		
		Token  s = null;
		
		JExpression        expr;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_throw);
		expr=jExpression();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JThrowStatement(sourceRef, expr, 
			utility.getStatementComment()); 
			
		}
		return self;
	}
	
	public final JAssertStatement  jAssertStatement(
		
	) throws RecognitionException, TokenStreamException {
		JAssertStatement self = null;
		
		Token  s = null;
		
		JExpression expr1;
		JExpression expr2 = null;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_assert);
		expr1=jExpression();
		{
		switch ( LA(1)) {
		case COLON:
		{
			match(COLON);
			expr2=jExpression();
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
			self = new JAssertStatement(sourceRef, expr1, expr2, 
			utility.getStatementComment()); 
			
		}
		return self;
	}
	
	public final JSynchronizedStatement  jSynchronizedStatement(
		
	) throws RecognitionException, TokenStreamException {
		JSynchronizedStatement self = null;
		
		Token  s = null;
		
		JExpression        expr;
		JStatement[]        body;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_synchronized);
		match(LPAREN);
		expr=jExpression();
		match(RPAREN);
		body=jCompoundStatement(null);
		if ( inputState.guessing==0 ) {
			
			self = new JSynchronizedStatement(sourceRef,
			expr, 
			new JBlock(sourceRef, body, null),
			utility.getStatementComment());
			
		}
		return self;
	}
	
	public final JSwitchGroup  jCasesGroup(
		
	) throws RecognitionException, TokenStreamException {
		JSwitchGroup self = null;
		
		
		ArrayList        labels = new ArrayList();
		ArrayList        stmts = new ArrayList();
		
		JSwitchLabel        label;
		JStatement        stmt;
		TokenReference    sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		int _cnt558=0;
		_loop558:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default) && (_tokenSet_44.member(LA(2)))) {
				label=jACase();
				if ( inputState.guessing==0 ) {
					labels.add(label);
				}
			}
			else {
				if ( _cnt558>=1 ) { break _loop558; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt558++;
		} while (true);
		}
		{
		_loop560:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				stmt=jStatement();
				if ( inputState.guessing==0 ) {
					
					if (stmt instanceof JEmptyStatement) {
					utility.reportTrouble(
					new CWarning(stmt.getTokenReference(), 
					MjcMessages.STRAY_SEMICOLON, null));
					}
					stmts.add(stmt);
					
				}
			}
			else {
				break _loop560;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new JSwitchGroup( sourceRef,
			(JSwitchLabel[]) labels.toArray( new JSwitchLabel[0] ), 
			(JStatement[]) stmts.toArray( new JStatement[0] ) );
			
			
			
		}
		return self;
	}
	
	public final JSwitchLabel  jACase(
		
	) throws RecognitionException, TokenStreamException {
		JSwitchLabel self = null;
		
		
		JExpression        expr = null;
		TokenReference    sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_case:
		{
			match(LITERAL_case);
			expr=jExpression();
			if ( inputState.guessing==0 ) {
				self = new JSwitchLabel(sourceRef, expr);
			}
			break;
		}
		case LITERAL_default:
		{
			match(LITERAL_default);
			if ( inputState.guessing==0 ) {
				self = new JSwitchLabel(sourceRef, null);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(COLON);
		return self;
	}
	
	public final JStatement  jForInit(
		
	) throws RecognitionException, TokenStreamException {
		JStatement self = null;
		
		
		JExpression[]    list;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		boolean synPredMatched567 = false;
		if (((_tokenSet_22.member(LA(1))) && (_tokenSet_23.member(LA(2))))) {
			int _m567 = mark();
			synPredMatched567 = true;
			inputState.guessing++;
			try {
				{
				jDeclaration();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched567 = false;
			}
			rewind(_m567);
inputState.guessing--;
		}
		if ( synPredMatched567 ) {
			self=jDeclaration();
		}
		else if ((_tokenSet_24.member(LA(1))) && (_tokenSet_45.member(LA(2)))) {
			list=jExpressionList();
			if ( inputState.guessing==0 ) {
				self = new JExpressionListStatement( sourceRef, 
				list, utility.getStatementComment());
			}
		}
		else if ((LA(1)==SEMI)) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		return self;
	}
	
	public final JExpression  jForCond(
		
	) throws RecognitionException, TokenStreamException {
		JExpression expr = null;
		
		
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			expr=jExpression();
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return expr;
	}
	
	public final JExpressionListStatement  jForIter(
		
	) throws RecognitionException, TokenStreamException {
		JExpressionListStatement self = null;
		
		
		JExpression[] list;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		{
		switch ( LA(1)) {
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_double:
		case LITERAL_false:
		case LITERAL_float:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_new:
		case LITERAL_null:
		case LITERAL_peer:
		case LITERAL_readonly:
		case LITERAL_rep:
		case LITERAL_resend:
		case LITERAL_short:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_true:
		case LITERAL_void:
		case LITERAL__warn:
		case LITERAL__warn_op:
		case LITERAL__nowarn:
		case LITERAL__nowarn_op:
		case BNOT:
		case DEC:
		case INC:
		case LNOT:
		case LPAREN:
		case MINUS:
		case PLUS:
		case CHARACTER_LITERAL:
		case IDENT:
		case INTEGER_LITERAL:
		case REAL_LITERAL:
		case STRING_LITERAL:
		case LITERAL_BS_bigint:
		case LITERAL_BS_bigint_math:
		case LITERAL_BS_duration:
		case LITERAL_BS_elemtype:
		case LITERAL_BS_fresh:
		case LITERAL_BS_invariant_for:
		case LITERAL_BS_is_initialized:
		case LITERAL_BS_java_math:
		case LITERAL_BS_lockset:
		case LITERAL_BS_max:
		case LITERAL_BS_nonnullelements:
		case LITERAL_BS_not_modified:
		case LITERAL_BS_not_assigned:
		case LITERAL_BS_nowarn:
		case LITERAL_BS_nowarn_op:
		case LITERAL_BS_old:
		case LITERAL_BS_only_assigned:
		case LITERAL_BS_only_accessed:
		case LITERAL_BS_only_called:
		case LITERAL_BS_only_captured:
		case LITERAL_BS_pre:
		case LITERAL_BS_reach:
		case LITERAL_BS_real:
		case LITERAL_BS_result:
		case LITERAL_BS_safe_math:
		case LITERAL_BS_space:
		case LITERAL_BS_type:
		case LITERAL_BS_typeof:
		case LITERAL_BS_warn:
		case LITERAL_BS_warn_op:
		case LITERAL_BS_working_space:
		case LITERAL_U_peer:
		case LITERAL_U_rep:
		case LITERAL_U_readonly:
		case INFORMAL_DESC:
		{
			list=jExpressionList();
			if ( inputState.guessing==0 ) {
				self = new JExpressionListStatement( sourceRef, list, null);
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return self;
	}
	
	public final JExpression[]  jExpressionList(
		
	) throws RecognitionException, TokenStreamException {
		JExpression[] self = null;
		
		
		JExpression        expr;
		ArrayList        vect = new ArrayList();
		
		
		expr=jExpression();
		if ( inputState.guessing==0 ) {
			vect.add(expr);
		}
		{
		_loop580:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				expr=jExpression();
				if ( inputState.guessing==0 ) {
					vect.add(expr);
				}
			}
			else {
				break _loop580;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			self = new JExpression[vect.size()];
			self = (JExpression[]) vect.toArray(self);
			
			
		}
		return self;
	}
	
	public final JCatchClause  jHandler(
		
	) throws RecognitionException, TokenStreamException {
		JCatchClause self = null;
		
		Token  s = null;
		
		JFormalParameter    param;
		JStatement[]        body;
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		s = LT(1);
		match(LITERAL_catch);
		match(LPAREN);
		param=jParameterDeclaration(JLocalVariable.DES_CATCH_PARAMETER);
		match(RPAREN);
		body=jCompoundStatement(null);
		if ( inputState.guessing==0 ) {
			
			self = new JCatchClause(sourceRef, 
			param, new JBlock(sourceRef, body, null)); 
			
		}
		return self;
	}
	
	public final JExpression  jLogicalAndExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression        right;
		
		
		self=jInclusiveOrExpression();
		{
		_loop589:
		do {
			if ((LA(1)==LAND)) {
				match(LAND);
				right=jInclusiveOrExpression();
				if ( inputState.guessing==0 ) {
					self = new JConditionalAndExpression(self.getTokenReference(), self, right);
				}
			}
			else {
				break _loop589;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jInclusiveOrExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression        right;
		
		
		self=jExclusiveOrExpression();
		{
		_loop592:
		do {
			if ((LA(1)==BOR)) {
				match(BOR);
				right=jExclusiveOrExpression();
				if ( inputState.guessing==0 ) {
					self = exprFactory.createBitwiseExpression(self.getTokenReference(), Constants.OPE_BOR, self, right);
				}
			}
			else {
				break _loop592;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jExclusiveOrExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression        right;
		
		
		self=jAndExpression();
		{
		_loop595:
		do {
			if ((LA(1)==BXOR)) {
				match(BXOR);
				right=jAndExpression();
				if ( inputState.guessing==0 ) {
					self = exprFactory.createBitwiseExpression(self.getTokenReference(), Constants.OPE_BXOR, self, right);
				}
			}
			else {
				break _loop595;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jAndExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression        right;
		
		
		self=jEqualityExpression();
		{
		_loop598:
		do {
			if ((LA(1)==BAND)) {
				match(BAND);
				right=jEqualityExpression();
				if ( inputState.guessing==0 ) {
					self = exprFactory.createBitwiseExpression(self.getTokenReference(), Constants.OPE_BAND, self, right);
				}
			}
			else {
				break _loop598;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jAdditiveExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op_p = null;
		Token  op_m = null;
		
		Token        op = null;
		JExpression  right;
		
		
		self=jMultiplicativeExpression();
		{
		_loop606:
		do {
			if ((LA(1)==MINUS||LA(1)==PLUS)) {
				{
				switch ( LA(1)) {
				case PLUS:
				{
					op_p = LT(1);
					match(PLUS);
					if ( inputState.guessing==0 ) {
						op = op_p;
					}
					break;
				}
				case MINUS:
				{
					op_m = LT(1);
					match(MINUS);
					if ( inputState.guessing==0 ) {
						op = op_m;
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				right=jMultiplicativeExpression();
				if ( inputState.guessing==0 ) {
					
					self = exprFactory.createAdditiveExpr(op, self.getTokenReference(), self, right);
					
				}
			}
			else {
				break _loop606;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jMultiplicativeExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op_m = null;
		Token  op_d = null;
		Token  op_r = null;
		
		Token        op = null;
		JExpression  right;
		
		
		self=jUnaryExpression();
		{
		_loop610:
		do {
			if ((_tokenSet_46.member(LA(1)))) {
				{
				switch ( LA(1)) {
				case STAR:
				{
					op_m = LT(1);
					match(STAR);
					if ( inputState.guessing==0 ) {
						op = op_m;
					}
					break;
				}
				case SLASH:
				{
					op_d = LT(1);
					match(SLASH);
					if ( inputState.guessing==0 ) {
						op = op_d;
					}
					break;
				}
				case PERCENT:
				{
					op_r = LT(1);
					match(PERCENT);
					if ( inputState.guessing==0 ) {
						op = op_r;
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				right=jUnaryExpression();
				if ( inputState.guessing==0 ) {
					
					self = exprFactory.createMultiplicativeExpr(op, self.getTokenReference(), self, right);
					
				}
			}
			else {
				break _loop610;
			}
			
		} while (true);
		}
		return self;
	}
	
	public final JExpression  jSuperSuffix(
		JSuperExpression supExpr
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  ident = null;
		
		JExpression[] args = null;
		
		
		switch ( LA(1)) {
		case LPAREN:
		{
			match(LPAREN);
			args=jArgList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new JExplicitConstructorInvocation(utility.buildTokenReference(), 
				supExpr.prefix(), Constants.JAV_SUPER, args);
			}
			break;
		}
		case DOT:
		{
			match(DOT);
			ident = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				self = new JNameExpression(utility.buildTokenReference(), supExpr, 
				ident.getText(), null);
			}
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				args=jArgList();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					self = new JMethodCallExpression(utility.buildTokenReference(), 
					self, args); 
					
				}
				break;
			}
			case LITERAL_for:
			case LITERAL_if:
			case LITERAL_instanceof:
			case ASSIGN:
			case BAND:
			case BAND_ASSIGN:
			case BOR:
			case BOR_ASSIGN:
			case BSR:
			case BSR_ASSIGN:
			case BXOR:
			case BXOR_ASSIGN:
			case COLON:
			case COMMA:
			case DEC:
			case DOT:
			case EQUAL:
			case GE:
			case GT:
			case INC:
			case LAND:
			case LBRACK:
			case LE:
			case LOR:
			case LT:
			case MINUS:
			case MINUS_ASSIGN:
			case NOT_EQUAL:
			case PERCENT:
			case PERCENT_ASSIGN:
			case PLUS:
			case PLUS_ASSIGN:
			case QUESTION:
			case RBRACK:
			case RCURLY:
			case RPAREN:
			case SEMI:
			case SL:
			case SLASH:
			case SLASH_ASSIGN:
			case SL_ASSIGN:
			case SR:
			case SR_ASSIGN:
			case STAR:
			case STAR_ASSIGN:
			case IDENT:
			case DOT_DOT:
			case IMPLIES:
			case BACKWARD_IMPLIES:
			case EQUIV:
			case NOT_EQUIV:
			case SUBTYPE_OF:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  mjResendSuffix(
		JExpression prefix
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		
		JExpression[] args = null;
		
		
		match(LPAREN);
		args=jArgList();
		match(RPAREN);
		if ( inputState.guessing==0 ) {
			self = new JResendExpression( utility.buildTokenReference(), prefix,
			args );
		}
		return self;
	}
	
	public final JExpression  jConstant(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  c = null;
		Token  s = null;
		Token  i = null;
		Token  r = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		
		
		switch ( LA(1)) {
		case CHARACTER_LITERAL:
		{
			c = LT(1);
			match(CHARACTER_LITERAL);
			if ( inputState.guessing==0 ) {
				self = new JCharLiteral(sourceRef, c.getText());
			}
			break;
		}
		case STRING_LITERAL:
		{
			s = LT(1);
			match(STRING_LITERAL);
			if ( inputState.guessing==0 ) {
				self = new JStringLiteral(sourceRef, 
				s.getText(), true);
			}
			break;
		}
		case INTEGER_LITERAL:
		{
			i = LT(1);
			match(INTEGER_LITERAL);
			if ( inputState.guessing==0 ) {
				self = new JOrdinalLiteral(sourceRef, i.getText());
			}
			break;
		}
		case REAL_LITERAL:
		{
			r = LT(1);
			match(REAL_LITERAL);
			if ( inputState.guessing==0 ) {
				self = new JRealLiteral(sourceRef, r.getText());
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	public final JExpression  mjWarnExpression(
		
	) throws RecognitionException, TokenStreamException {
		JExpression self = null;
		
		Token  op1 = null;
		Token  op2 = null;
		Token  op3 = null;
		Token  op4 = null;
		
		TokenReference sourceRef = utility.buildTokenReference( LT(1) );
		JExpression expr = null;
		
		
		switch ( LA(1)) {
		case LITERAL__warn:
		{
			op1 = LT(1);
			match(LITERAL__warn);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op1.getText(), expr, true);
			}
			break;
		}
		case LITERAL__warn_op:
		{
			op2 = LT(1);
			match(LITERAL__warn_op);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op2.getText(), expr, true, true);
			}
			break;
		}
		case LITERAL__nowarn:
		{
			op3 = LT(1);
			match(LITERAL__nowarn);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op3.getText(), expr, false);
			}
			break;
		}
		case LITERAL__nowarn_op:
		{
			op4 = LT(1);
			match(LITERAL__nowarn_op);
			match(LPAREN);
			expr=jExpression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				self = new MJWarnExpression(sourceRef, op4.getText(), expr, false, true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return self;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"abstract\"",
		"\"assert\"",
		"\"boolean\"",
		"\"break\"",
		"\"byte\"",
		"\"case\"",
		"\"catch\"",
		"\"char\"",
		"\"class\"",
		"\"const\"",
		"\"continue\"",
		"\"default\"",
		"\"do\"",
		"\"double\"",
		"\"else\"",
		"\"extends\"",
		"\"false\"",
		"\"final\"",
		"\"finally\"",
		"\"float\"",
		"\"for\"",
		"\"goto\"",
		"\"if\"",
		"\"implements\"",
		"\"import\"",
		"\"instanceof\"",
		"\"int\"",
		"\"interface\"",
		"\"long\"",
		"\"native\"",
		"\"new\"",
		"\"null\"",
		"\"package\"",
		"\"private\"",
		"\"protected\"",
		"\"public\"",
		"\"peer\"",
		"\"readonly\"",
		"\"rep\"",
		"\"pure\"",
		"\"resend\"",
		"\"return\"",
		"\"short\"",
		"\"static\"",
		"\"strictfp\"",
		"\"super\"",
		"\"switch\"",
		"\"synchronized\"",
		"\"this\"",
		"\"throw\"",
		"\"throws\"",
		"\"transient\"",
		"\"true\"",
		"\"try\"",
		"\"void\"",
		"\"volatile\"",
		"\"while\"",
		"\"_warn\"",
		"\"_warn_op\"",
		"\"_nowarn\"",
		"\"_nowarn_op\"",
		"'='",
		"'@'",
		"'&'",
		"'&='",
		"'~'",
		"'|'",
		"'|='",
		"'>>>'",
		"'>>>='",
		"'^'",
		"'^='",
		"':'",
		"','",
		"'--'",
		"'.'",
		"'=='",
		"'>='",
		"'>'",
		"'++'",
		"'&&'",
		"'['",
		"'{'",
		"'<='",
		"'!'",
		"'||'",
		"'('",
		"'<'",
		"'-'",
		"'-='",
		"'!='",
		"'%'",
		"'%='",
		"'+'",
		"'+='",
		"'?'",
		"']'",
		"'}'",
		"')'",
		"';'",
		"'<<'",
		"'/'",
		"'/='",
		"'<<='",
		"'>>'",
		"'>>='",
		"'*'",
		"'*='",
		"a character literal (inside simple quotes)",
		"an identifier",
		"an integer literal",
		"a real literal",
		"a string literal (inside double quotes)",
		"'/**'",
		"'..'",
		"\"\\\\TYPE\"",
		"\"\\\\bigint\"",
		"\"\\\\bigint_math\"",
		"\"\\\\duration\"",
		"\"\\\\elemtype\"",
		"\"\\\\everything\"",
		"\"\\\\exists\"",
		"\"\\\\forall\"",
		"\"\\\\fresh\"",
		"\"\\\\into\"",
		"\"\\\\invariant_for\"",
		"\"\\\\is_initialized\"",
		"\"\\\\java_math\"",
		"\"\\\\lblneg\"",
		"\"\\\\lblpos\"",
		"\"\\\\lockset\"",
		"\"\\\\max\"",
		"\"\\\\min\"",
		"\"\\\\nonnullelements\"",
		"\"\\\\not_modified\"",
		"\"\\\\not_assigned\"",
		"\"\\\\not_specified\"",
		"\"\\\\nothing\"",
		"\"\\\\nowarn\"",
		"\"\\\\nowarn_op\"",
		"\"\\\\num_of\"",
		"\"\\\\old\"",
		"\"\\\\only_assigned\"",
		"\"\\\\only_accessed\"",
		"\"\\\\only_called\"",
		"\"\\\\only_captured\"",
		"\"\\\\other\"",
		"\"\\\\pre\"",
		"\"\\\\product\"",
		"\"\\\\reach\"",
		"\"\\\\real\"",
		"\"\\\\result\"",
		"\"\\\\safe_math\"",
		"\"\\\\same\"",
		"\"\\\\space\"",
		"\"\\\\such_that\"",
		"\"\\\\sum\"",
		"\"\\\\type\"",
		"\"\\\\typeof\"",
		"\"\\\\warn\"",
		"\"\\\\warn_op\"",
		"\"\\\\working_space\"",
		"\"\\\\peer\"",
		"\"\\\\rep\"",
		"\"\\\\readonly\"",
		"\"abrupt_behavior\"",
		"\"abrupt_behaviour\"",
		"\"accessible\"",
		"\"accessible_redundantly\"",
		"\"also\"",
		"\"assert_redundantly\"",
		"\"assignable\"",
		"\"assignable_redundantly\"",
		"\"assume\"",
		"\"assume_redundantly\"",
		"\"axiom\"",
		"\"behavior\"",
		"\"behaviour\"",
		"\"breaks\"",
		"\"breaks_redundantly\"",
		"\"callable\"",
		"\"callable_redundantly\"",
		"\"captures\"",
		"\"captures_redundantly\"",
		"\"choose\"",
		"\"choose_if\"",
		"\"code\"",
		"\"code_bigint_math\"",
		"\"code_contract\"",
		"\"code_java_math\"",
		"\"code_safe_math\"",
		"\"constraint\"",
		"\"constraint_redundantly\"",
		"\"constructor\"",
		"\"continues\"",
		"\"continues_redundantly\"",
		"\"debug\"",
		"\"decreases\"",
		"\"decreases_redundantly\"",
		"\"decreasing\"",
		"\"decreasing_redundantly\"",
		"\"diverges\"",
		"\"diverges_redundantly\"",
		"\"duration\"",
		"\"duration_redundantly\"",
		"\"ensures\"",
		"\"ensures_redundantly\"",
		"\"example\"",
		"\"exceptional_behavior\"",
		"\"exceptional_behaviour\"",
		"\"exceptional_example\"",
		"\"exsures\"",
		"\"exsures_redundantly\"",
		"\"extract\"",
		"\"field\"",
		"\"forall\"",
		"\"for_example\"",
		"\"ghost\"",
		"\"helper\"",
		"\"hence_by\"",
		"\"hence_by_redundantly\"",
		"\"implies_that\"",
		"\"in\"",
		"\"in_redundantly\"",
		"\"initializer\"",
		"\"initially\"",
		"\"instance\"",
		"\"invariant\"",
		"\"invariant_redundantly\"",
		"\"loop_invariant\"",
		"\"loop_invariant_redundantly\"",
		"\"maintaining\"",
		"\"maintaining_redundantly\"",
		"\"maps\"",
		"\"maps_redundantly\"",
		"\"measured_by\"",
		"\"measured_by_redundantly\"",
		"\"method\"",
		"\"model\"",
		"\"model_program\"",
		"\"modifiable\"",
		"\"modifiable_redundantly\"",
		"\"modifies\"",
		"\"modifies_redundantly\"",
		"\"monitored\"",
		"\"monitors_for\"",
		"\"non_null\"",
		"\"non_null_by_default\"",
		"\"normal_behavior\"",
		"\"normal_behaviour\"",
		"\"normal_example\"",
		"\"nullable\"",
		"\"nullable_by_default\"",
		"\"old\"",
		"\"or\"",
		"\"post\"",
		"\"post_redundantly\"",
		"\"pre\"",
		"\"pre_redundantly\"",
		"\"query\"",
		"\"readable\"",
		"\"refine\"",
		"\"refines\"",
		"\"refining\"",
		"\"represents\"",
		"\"represents_redundantly\"",
		"\"requires\"",
		"\"requires_redundantly\"",
		"\"returns\"",
		"\"returns_redundantly\"",
		"\"secret\"",
		"\"set\"",
		"\"signals\"",
		"\"signals_only\"",
		"\"signals_only_redundantly\"",
		"\"signals_redundantly\"",
		"\"spec_bigint_math\"",
		"\"spec_java_math\"",
		"\"spec_protected\"",
		"\"spec_public\"",
		"\"spec_safe_math\"",
		"\"static_initializer\"",
		"\"uninitialized\"",
		"\"unreachable\"",
		"\"weakly\"",
		"\"when\"",
		"\"when_redundantly\"",
		"\"working_space\"",
		"\"working_space_redundantly\"",
		"\"writable\"",
		"(* ... *)",
		"'==>'",
		"'<=='",
		"'<==>'",
		"'<=!=>'",
		"'->'",
		"'<-'",
		"'<:'",
		"'{|'",
		"'|}'",
		"AFFIRM"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = new long[10];
		data[0]=903481777360869712L;
		data[1]=108649890766127104L;
		data[2]=-3462782404119232512L;
		data[3]=-4755941658448109370L;
		data[4]=70499203268859L;
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 2147487744L, 549755813888L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = new long[10];
		data[0]=903481775213381968L;
		data[1]=108649341010313216L;
		data[2]=-3462782404119232512L;
		data[3]=-4755941658448109370L;
		data[4]=70499203268859L;
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { 7696581394432L, 0L, 1924145348608L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 288300750273120576L, 72057594037927936L, 67108864L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = new long[10];
		data[0]=615173328576970768L;
		data[1]=18767552808599262L;
		data[2]=-3462784328331689984L;
		data[3]=-4756504608401530682L;
		data[4]=78749835444475L;
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = new long[10];
		data[0]=615173328358866960L;
		data[2]=-9223372036854775808L;
		data[3]=-8285497137932795898L;
		data[4]=1594097793L;
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = new long[10];
		data[0]=903481777360869712L;
		data[1]=108649890904539136L;
		data[2]=-3460530604305547264L;
		data[3]=-138665166642946L;
		data[4]=70636642234875L;
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = new long[10];
		data[0]=-18014470354544144L;
		data[1]=-8097753046286057439L;
		data[2]=-5749328716455031090L;
		data[3]=-4826697983050375418L;
		data[4]=281753596725377L;
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = new long[10];
		data[0]=903481775213381968L;
		data[1]=108649341144530944L;
		data[2]=-9223370112642318336L;
		data[3]=-8284934187979374554L;
		data[4]=1594097793L;
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = new long[10];
		data[0]=903481775213381968L;
		data[1]=108649341213769728L;
		data[2]=-9223370112642318336L;
		data[3]=-8284934187979374554L;
		data[4]=1594097793L;
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = { 288308446854515008L, 108649341144530944L, 1924212457472L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = { 288308446854515008L, 72620544127696896L, 1924212457472L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 0L, 549757919234L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = new long[8];
		data[3]=105604655874048L;
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = { 288308446854515008L, 108649341010313216L, 1924212457472L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = new long[10];
		data[2]=1135355706841497600L;
		data[3]=67976206901305536L;
		data[4]=70497609121816L;
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	private static final long[] mk_tokenSet_17() {
		long[] data = new long[10];
		data[0]=-18014470354248720L;
		data[1]=-8097752908712886239L;
		data[2]=-5749293532082942258L;
		data[3]=-4826134955519107290L;
		data[4]=422491621951617L;
		return data;
	}
	public static final BitSet _tokenSet_17 = new BitSet(mk_tokenSet_17());
	private static final long[] mk_tokenSet_18() {
		long[] data = new long[10];
		data[4]=49248L;
		return data;
	}
	public static final BitSet _tokenSet_18 = new BitSet(mk_tokenSet_18());
	private static final long[] mk_tokenSet_19() {
		long[] data = new long[10];
		data[2]=1135355706841497600L;
		data[3]=67976206901305536L;
		data[4]=128864944152L;
		return data;
	}
	public static final BitSet _tokenSet_19 = new BitSet(mk_tokenSet_19());
	private static final long[] mk_tokenSet_20() {
		long[] data = new long[8];
		data[1]=562949953421312L;
		data[3]=-8935141660703064064L;
		return data;
	}
	public static final BitSet _tokenSet_20 = new BitSet(mk_tokenSet_20());
	private static final long[] mk_tokenSet_21() {
		long[] data = new long[10];
		data[0]=-1940392775013758656L;
		data[1]=-8133782393060835295L;
		data[2]=2192022884046L;
		data[4]=274877906944L;
		return data;
	}
	public static final BitSet _tokenSet_21 = new BitSet(mk_tokenSet_21());
	private static final long[] mk_tokenSet_22() {
		long[] data = new long[10];
		data[0]=903481775213381968L;
		data[1]=108649341010313216L;
		data[2]=-9223370112642318336L;
		data[3]=-8285497137932795898L;
		data[4]=1594097793L;
		return data;
	}
	public static final BitSet _tokenSet_22 = new BitSet(mk_tokenSet_22());
	private static final long[] mk_tokenSet_23() {
		long[] data = new long[10];
		data[0]=903481775213381968L;
		data[1]=108649341146660864L;
		data[2]=-9223370112642318336L;
		data[3]=-8285497137932795898L;
		data[4]=1594097793L;
		return data;
	}
	public static final BitSet _tokenSet_23 = new BitSet(mk_tokenSet_23());
	private static final long[] mk_tokenSet_24() {
		long[] data = new long[10];
		data[0]=-1940392775013758656L;
		data[1]=-8133782393065029599L;
		data[2]=2192022884046L;
		data[4]=274877906944L;
		return data;
	}
	public static final BitSet _tokenSet_24 = new BitSet(mk_tokenSet_24());
	private static final long[] mk_tokenSet_25() {
		long[] data = new long[10];
		data[0]=-1940392774476887744L;
		data[1]=-1215972380430577669L;
		data[2]=2196334694398L;
		data[3]=-8935141660703064064L;
		data[4]=43705587204096L;
		return data;
	}
	public static final BitSet _tokenSet_25 = new BitSet(mk_tokenSet_25());
	private static final long[] mk_tokenSet_26() {
		long[] data = { 288308446854515008L, 72057594037927936L, 1924212457472L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_26 = new BitSet(mk_tokenSet_26());
	private static final long[] mk_tokenSet_27() {
		long[] data = { 7696581394432L, 562949953421312L, 1924145348608L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_27 = new BitSet(mk_tokenSet_27());
	private static final long[] mk_tokenSet_28() {
		long[] data = new long[10];
		data[0]=-1940392775013758656L;
		data[1]=-8133782401940717567L;
		data[2]=2192022884046L;
		data[4]=274877906944L;
		return data;
	}
	public static final BitSet _tokenSet_28 = new BitSet(mk_tokenSet_28());
	private static final long[] mk_tokenSet_29() {
		long[] data = new long[10];
		data[0]=-1940392774393001664L;
		data[1]=-1197957500884746245L;
		data[2]=2196334694398L;
		data[3]=-8935141660703064064L;
		data[4]=43705587204096L;
		return data;
	}
	public static final BitSet _tokenSet_29 = new BitSet(mk_tokenSet_29());
	private static final long[] mk_tokenSet_30() {
		long[] data = new long[10];
		data[0]=-18014470354248720L;
		data[1]=-8097752908847103967L;
		data[2]=-5749328716455031090L;
		data[3]=-4826697983050375418L;
		data[4]=281753596725377L;
		return data;
	}
	public static final BitSet _tokenSet_30 = new BitSet(mk_tokenSet_30());
	private static final long[] mk_tokenSet_31() {
		long[] data = new long[10];
		data[0]=-18014467665698830L;
		data[1]=-1179943445968461829L;
		data[2]=-2688561154L;
		data[3]=-4611791623087980546L;
		data[4]=395819891030527L;
		return data;
	}
	public static final BitSet _tokenSet_31 = new BitSet(mk_tokenSet_31());
	private static final long[] mk_tokenSet_32() {
		long[] data = new long[10];
		data[0]=-18014470354248720L;
		data[1]=-8097752908847103967L;
		data[2]=-5749293532082942258L;
		data[3]=-4826697983050375418L;
		data[4]=422491085080705L;
		return data;
	}
	public static final BitSet _tokenSet_32 = new BitSet(mk_tokenSet_32());
	private static final long[] mk_tokenSet_33() {
		long[] data = { 0L, 142999552L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_33 = new BitSet(mk_tokenSet_33());
	private static final long[] mk_tokenSet_34() {
		long[] data = { 0L, 18691697672448L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_34 = new BitSet(mk_tokenSet_34());
	private static final long[] mk_tokenSet_35() {
		long[] data = new long[10];
		data[0]=620756992L;
		data[1]=18858823351533530L;
		data[4]=43430709297152L;
		return data;
	}
	public static final BitSet _tokenSet_35 = new BitSet(mk_tokenSet_35());
	private static final long[] mk_tokenSet_36() {
		long[] data = new long[10];
		data[0]=-18014467669894158L;
		data[1]=-6926536226895822853L;
		data[2]=-4852887857L;
		data[3]=-4611686018432106498L;
		data[4]=554149565430267L;
		return data;
	}
	public static final BitSet _tokenSet_36 = new BitSet(mk_tokenSet_36());
	private static final long[] mk_tokenSet_37() {
		long[] data = new long[10];
		data[0]=-1940392774476887744L;
		data[1]=-1215972655308484613L;
		data[2]=2196334694398L;
		data[3]=-8935141660703064064L;
		data[4]=43705587204096L;
		return data;
	}
	public static final BitSet _tokenSet_37 = new BitSet(mk_tokenSet_37());
	private static final long[] mk_tokenSet_38() {
		long[] data = { 0L, 6917529027641081856L, 4311810432L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_38 = new BitSet(mk_tokenSet_38());
	private static final long[] mk_tokenSet_39() {
		long[] data = new long[8];
		data[0]=288308446854515008L;
		data[1]=108649341010313216L;
		data[2]=1924212457472L;
		data[3]=-8935141660703064064L;
		return data;
	}
	public static final BitSet _tokenSet_39 = new BitSet(mk_tokenSet_39());
	private static final long[] mk_tokenSet_40() {
		long[] data = new long[8];
		data[0]=288300750273120576L;
		data[1]=72620543991349248L;
		data[2]=67108864L;
		data[3]=-8935141660703064064L;
		return data;
	}
	public static final BitSet _tokenSet_40 = new BitSet(mk_tokenSet_40());
	private static final long[] mk_tokenSet_41() {
		long[] data = { 288300750273120576L, 72620543991349248L, 67108864L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_41 = new BitSet(mk_tokenSet_41());
	private static final long[] mk_tokenSet_42() {
		long[] data = { 0L, 207650816L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_42 = new BitSet(mk_tokenSet_42());
	private static final long[] mk_tokenSet_43() {
		long[] data = new long[10];
		data[0]=-1940392775013758656L;
		data[1]=-8133782324345552863L;
		data[2]=2192022884046L;
		data[4]=274877906944L;
		return data;
	}
	public static final BitSet _tokenSet_43 = new BitSet(mk_tokenSet_43());
	private static final long[] mk_tokenSet_44() {
		long[] data = new long[10];
		data[0]=-1940392775013758656L;
		data[1]=-8133782393065025503L;
		data[2]=2192022884046L;
		data[4]=274877906944L;
		return data;
	}
	public static final BitSet _tokenSet_44 = new BitSet(mk_tokenSet_44());
	private static final long[] mk_tokenSet_45() {
		long[] data = new long[10];
		data[0]=-1940392774476887744L;
		data[1]=-1215972380430569477L;
		data[2]=2196334694398L;
		data[3]=-8935141660703064064L;
		data[4]=43705587204096L;
		return data;
	}
	public static final BitSet _tokenSet_45 = new BitSet(mk_tokenSet_45());
	private static final long[] mk_tokenSet_46() {
		long[] data = { 0L, 72569914916864L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_46 = new BitSet(mk_tokenSet_46());
	
	}
