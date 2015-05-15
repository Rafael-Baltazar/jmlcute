// $ANTLR 2.7.7 (20070227): "expandedJmlML.g" -> "JmlMLLexer.java"$
 
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
 * $Id: JmlML.g,v 1.15 2005/06/09 10:42:47 davidcok Exp $
 */

    package org.jmlspecs.checker; 

    import java.io.InputStream;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Hashtable;

import org.multijava.mjc.MjcMessages;
import org.multijava.mjc.MjcTokenTypes;
import org.multijava.mjc.ParsingController;
import org.multijava.util.Message;
import org.multijava.util.compiler.CToken;
import org.multijava.util.compiler.CWarning;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.TroubleReporter;

import antlr.ANTLRHashString;
import antlr.ByteBuffer;
import antlr.CharBuffer;
import antlr.CharStreamException;
import antlr.CharStreamIOException;
import antlr.InputBuffer;
import antlr.LexerSharedInputState;
import antlr.NoViableAltForCharException;
import antlr.RecognitionException;
import antlr.SemanticException;
import antlr.Token;
import antlr.TokenStream;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.TokenStreamRecognitionException;
import antlr.collections.impl.BitSet;

    /**
	 * This is the scanner for multi-line JML annotations. */

public class JmlMLLexer extends antlr.CharScanner implements JmlMLLexerTokenTypes, TokenStream
 {

    public JmlMLLexer(ParsingController parsingController,
	TokenStreamSelector lexingController, boolean allowJavaAssert, 
        boolean allowResend, 
        boolean allowUniverseKeywords, // WMD
        TroubleReporter reporter ) 
    {
	this( parsingController.sharedInputState() );
	this.parsingController = parsingController;
	this.lexingController = lexingController;
        this.allowJavaAssert = allowJavaAssert;
	this.allowResend = allowResend;
    this.allowUniverseKeywords = allowUniverseKeywords; // WMD
    lexingController.setAllowUniverseKeywords( allowUniverseKeywords ); // WMD
        this.reporter = reporter;
    }

    /**
     * If tok represents a conditionally reserved word that is not 
     * reserved during this lexical analysis, then returns null, otherwise
     * returns tok.  For reserved words whose non-reserved use will be
     * deprecated (e.g., 'assert'), throws an . */
    private Token checkReservedTokens(Token tok) {
	if (tok == null) { return null; }
	Token result = tok;
	switch (tok.getType()) {
	    case MjcTokenTypes.LITERAL_assert:
	    if (!allowJavaAssert) {
		reporter.reportTrouble(
		    new CWarning(
			TokenReference.build( parsingController.file(),
			    getLine(), getColumn()), 
			MjcMessages.ASSERT_IS_KEYWORD));
		result = null;
	    }
	    break;
	    
	    case MjcTokenTypes.LITERAL_resend:
	    if (!allowResend) {
		result = null;
	    }
	    break;


        case JmlTokenTypes.LITERAL_secret:
        case JmlTokenTypes.LITERAL_query:
            if (!Main.hasOptionXobspure()) result = null;
            break;


        // WMD
        case MjcTokenTypes.LITERAL_peer:
        case MjcTokenTypes.LITERAL_readonly:
        case MjcTokenTypes.LITERAL_rep:
            if( !allowUniverseKeywords ) {
                result = null;
            }
            break;


        // WMD allow the pure token for JML
        case MjcTokenTypes.LITERAL_pure:
            if( !inAnnotation && !allowUniverseKeywords ) {
                result = null;
            }
            break;
	}
	return result;
    }

    /**
	 * Called by the scanner when a tab is detected in the input
	 * stream.  Advances the column number according to tabSize.
	 *
	 * @see	#setTabSize(int)
	 * @see #tabSize() */
    public void tab() {
	setColumn( getColumn() + tabSize );
    }
    
    /**
	 * Sets the amount by which the column number is incremented when
	 * a tab character is detected in the input stream. 
	 *
	 * @see #tabSize() */
    public void setTabSize( int ts ) { tabSize = ts; }

    /**
	 * Indicates the amount by which the column number is incremented
	 * when a tab character is detected in the input stream.
	 *
	 * @see #setTabSize(int) */
    public int tabSize() { return tabSize; }

    /**
	 * The amount by which the column number is incremented when a tab
	 * character is detected in the input stream.  */
    private int tabSize = 8;

    /**
	 * Used to switch lexers for nested languages (i.e., javadoc).
	 * Aliases should be established in all lexers that share the same
	 * input stream. */
    private ParsingController parsingController;

    /**
	 * Used to switch lexers when moving in and out of
	 * annotations. Aliases should be established in all lexers that
	 * share the same input stream. */
    private TokenStreamSelector lexingController;

    /**
	 * Used to convert token text from String to char[]. */
    private char[] charCache = null;

    /**
	 * Flag indicates whether we are lexing within an annotation.  A
	 * different definition of IDENT (allowing leading '\') is used in
	 * this case and a different keyword table is consulted for
	 * resolving IDENTs.  */
    private boolean inAnnotation = true;

    /**
	 * Flag indicates whether we are lexing within a JML expression.  Used
     * to switch between keyword tables for resolving IDENTs.
     */
    private boolean inJMLExpression = false;

    /**
	 * Flag indicates whether we are lexing within a JML quantifier
     * expression.  Used to detect whether or not a ';' indicates the
     * end of a JML expression.
     */
    private boolean inQuantifier = false;

    /**
     * Count of the number of left parens without matching right
     * parens found within a JML expression.  Used to detect whether
     * or not a ';' indicates the end of a JML expression.
     */
    private int parenCount = 0;

    /**
	 * Flag indicates whether annotations should be allowed.  Used to
	 * prohibit nested annotations.
	 *
	 * <pre><jml>
	 * private invariant allowAnnotations <==> (* this is not an annotation lexer *);
	 * </jml></pre>
	 * */
    private final boolean allowAnnotations = false;

    /*
     * Indicate which conditionally reserved words should be
     * reserved during this analysis.
     */
    private boolean allowJavaAssert;
    private boolean allowResend;

    // WMD
    private boolean allowUniverseKeywords;

    /**
     * Used to report warnings during lexing.
     */
    private TroubleReporter reporter;
public JmlMLLexer(InputStream in) {
	this(new ByteBuffer(in));
}
public JmlMLLexer(Reader in) {
	this(new CharBuffer(in));
}
public JmlMLLexer(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public JmlMLLexer(LexerSharedInputState state) {
	super(state);
	caseSensitiveLiterals = true;
	setCaseSensitive(true);
	literals = new Hashtable();
	literals.put(new ANTLRHashString("working_space_redundantly", this), new Integer(292));
	literals.put(new ANTLRHashString("maps_redundantly", this), new Integer(238));
	literals.put(new ANTLRHashString("implies_that", this), new Integer(225));
	literals.put(new ANTLRHashString("signals_redundantly", this), new Integer(279));
	literals.put(new ANTLRHashString("abstract", this), new Integer(4));
	literals.put(new ANTLRHashString("\\lockset", this), new Integer(134));
	literals.put(new ANTLRHashString("void", this), new Integer(58));
	literals.put(new ANTLRHashString("also", this), new Integer(173));
	literals.put(new ANTLRHashString("accessible_redundantly", this), new Integer(172));
	literals.put(new ANTLRHashString("\\such_that", this), new Integer(159));
	literals.put(new ANTLRHashString("\\lblneg", this), new Integer(132));
	literals.put(new ANTLRHashString("maps", this), new Integer(237));
	literals.put(new ANTLRHashString("secret", this), new Integer(274));
	literals.put(new ANTLRHashString("static", this), new Integer(47));
	literals.put(new ANTLRHashString("in_redundantly", this), new Integer(227));
	literals.put(new ANTLRHashString("behaviour", this), new Integer(181));
	literals.put(new ANTLRHashString("signals", this), new Integer(276));
	literals.put(new ANTLRHashString("pure", this), new Integer(43));
	literals.put(new ANTLRHashString("\\other", this), new Integer(150));
	literals.put(new ANTLRHashString("modifiable_redundantly", this), new Integer(245));
	literals.put(new ANTLRHashString("weakly", this), new Integer(288));
	literals.put(new ANTLRHashString("invariant_redundantly", this), new Integer(232));
	literals.put(new ANTLRHashString("import", this), new Integer(28));
	literals.put(new ANTLRHashString("break", this), new Integer(7));
	literals.put(new ANTLRHashString("\\result", this), new Integer(155));
	literals.put(new ANTLRHashString("non_null", this), new Integer(250));
	literals.put(new ANTLRHashString("assert_redundantly", this), new Integer(174));
	literals.put(new ANTLRHashString("readonly", this), new Integer(41));
	literals.put(new ANTLRHashString("_warn_op", this), new Integer(62));
	literals.put(new ANTLRHashString("_warn", this), new Integer(61));
	literals.put(new ANTLRHashString("constructor", this), new Integer(197));
	literals.put(new ANTLRHashString("continue", this), new Integer(14));
	literals.put(new ANTLRHashString("catch", this), new Integer(10));
	literals.put(new ANTLRHashString("helper", this), new Integer(222));
	literals.put(new ANTLRHashString("for", this), new Integer(24));
	literals.put(new ANTLRHashString("refine", this), new Integer(265));
	literals.put(new ANTLRHashString("else", this), new Integer(18));
	literals.put(new ANTLRHashString("\\product", this), new Integer(152));
	literals.put(new ANTLRHashString("assume_redundantly", this), new Integer(178));
	literals.put(new ANTLRHashString("\\pre", this), new Integer(151));
	literals.put(new ANTLRHashString("\\not_modified", this), new Integer(138));
	literals.put(new ANTLRHashString("byte", this), new Integer(8));
	literals.put(new ANTLRHashString("interface", this), new Integer(31));
	literals.put(new ANTLRHashString("float", this), new Integer(23));
	literals.put(new ANTLRHashString("\\nothing", this), new Integer(141));
	literals.put(new ANTLRHashString("continues", this), new Integer(198));
	literals.put(new ANTLRHashString("throws", this), new Integer(54));
	literals.put(new ANTLRHashString("assume", this), new Integer(177));
	literals.put(new ANTLRHashString("decreasing_redundantly", this), new Integer(204));
	literals.put(new ANTLRHashString("forall", this), new Integer(219));
	literals.put(new ANTLRHashString("exsures_redundantly", this), new Integer(216));
	literals.put(new ANTLRHashString("decreases_redundantly", this), new Integer(202));
	literals.put(new ANTLRHashString("behavior", this), new Integer(180));
	literals.put(new ANTLRHashString("\\only_captured", this), new Integer(149));
	literals.put(new ANTLRHashString("spec_public", this), new Integer(283));
	literals.put(new ANTLRHashString("\\max", this), new Integer(135));
	literals.put(new ANTLRHashString("\\typeof", this), new Integer(162));
	literals.put(new ANTLRHashString("method", this), new Integer(241));
	literals.put(new ANTLRHashString("captures_redundantly", this), new Integer(187));
	literals.put(new ANTLRHashString("modifies", this), new Integer(246));
	literals.put(new ANTLRHashString("strictfp", this), new Integer(48));
	literals.put(new ANTLRHashString("private", this), new Integer(37));
	literals.put(new ANTLRHashString("\\forall", this), new Integer(126));
	literals.put(new ANTLRHashString("model_program", this), new Integer(243));
	literals.put(new ANTLRHashString("post", this), new Integer(259));
	literals.put(new ANTLRHashString("duration_redundantly", this), new Integer(208));
	literals.put(new ANTLRHashString("unreachable", this), new Integer(287));
	literals.put(new ANTLRHashString("\\nowarn", this), new Integer(142));
	literals.put(new ANTLRHashString("throw", this), new Integer(53));
	literals.put(new ANTLRHashString("instance", this), new Integer(230));
	literals.put(new ANTLRHashString("\\nonnullelements", this), new Integer(137));
	literals.put(new ANTLRHashString("spec_protected", this), new Integer(282));
	literals.put(new ANTLRHashString("non_null_by_default", this), new Integer(251));
	literals.put(new ANTLRHashString("\\elemtype", this), new Integer(123));
	literals.put(new ANTLRHashString("peer", this), new Integer(40));
	literals.put(new ANTLRHashString("short", this), new Integer(46));
	literals.put(new ANTLRHashString("monitored", this), new Integer(248));
	literals.put(new ANTLRHashString("pre_redundantly", this), new Integer(262));
	literals.put(new ANTLRHashString("invariant", this), new Integer(231));
	literals.put(new ANTLRHashString("long", this), new Integer(32));
	literals.put(new ANTLRHashString("measured_by", this), new Integer(239));
	literals.put(new ANTLRHashString("try", this), new Integer(57));
	literals.put(new ANTLRHashString("\\rep", this), new Integer(167));
	literals.put(new ANTLRHashString("\\lblpos", this), new Integer(133));
	literals.put(new ANTLRHashString("nullable_by_default", this), new Integer(256));
	literals.put(new ANTLRHashString("debug", this), new Integer(200));
	literals.put(new ANTLRHashString("refines", this), new Integer(266));
	literals.put(new ANTLRHashString("in", this), new Integer(226));
	literals.put(new ANTLRHashString("loop_invariant_redundantly", this), new Integer(234));
	literals.put(new ANTLRHashString("\\warn_op", this), new Integer(164));
	literals.put(new ANTLRHashString("switch", this), new Integer(50));
	literals.put(new ANTLRHashString("requires", this), new Integer(270));
	literals.put(new ANTLRHashString("\\type", this), new Integer(161));
	literals.put(new ANTLRHashString("spec_bigint_math", this), new Integer(280));
	literals.put(new ANTLRHashString("\\same", this), new Integer(157));
	literals.put(new ANTLRHashString("spec_safe_math", this), new Integer(284));
	literals.put(new ANTLRHashString("\\not_assigned", this), new Integer(139));
	literals.put(new ANTLRHashString("signals_only_redundantly", this), new Integer(278));
	literals.put(new ANTLRHashString("this", this), new Integer(52));
	literals.put(new ANTLRHashString("\\safe_math", this), new Integer(156));
	literals.put(new ANTLRHashString("when", this), new Integer(289));
	literals.put(new ANTLRHashString("null", this), new Integer(35));
	literals.put(new ANTLRHashString("modifiable", this), new Integer(244));
	literals.put(new ANTLRHashString("abrupt_behaviour", this), new Integer(170));
	literals.put(new ANTLRHashString("abrupt_behavior", this), new Integer(169));
	literals.put(new ANTLRHashString("decreasing", this), new Integer(203));
	literals.put(new ANTLRHashString("\\working_space", this), new Integer(165));
	literals.put(new ANTLRHashString("refining", this), new Integer(267));
	literals.put(new ANTLRHashString("\\not_specified", this), new Integer(140));
	literals.put(new ANTLRHashString("\\reach", this), new Integer(153));
	literals.put(new ANTLRHashString("public", this), new Integer(39));
	literals.put(new ANTLRHashString("hence_by_redundantly", this), new Integer(224));
	literals.put(new ANTLRHashString("\\only_called", this), new Integer(148));
	literals.put(new ANTLRHashString("normal_behavior", this), new Integer(252));
	literals.put(new ANTLRHashString("pre", this), new Integer(261));
	literals.put(new ANTLRHashString("\\warn", this), new Integer(163));
	literals.put(new ANTLRHashString("extends", this), new Integer(19));
	literals.put(new ANTLRHashString("constraint_redundantly", this), new Integer(196));
	literals.put(new ANTLRHashString("example", this), new Integer(211));
	literals.put(new ANTLRHashString("false", this), new Integer(20));
	literals.put(new ANTLRHashString("spec_java_math", this), new Integer(281));
	literals.put(new ANTLRHashString("decreases", this), new Integer(201));
	literals.put(new ANTLRHashString("diverges", this), new Integer(205));
	literals.put(new ANTLRHashString("callable", this), new Integer(184));
	literals.put(new ANTLRHashString("\\readonly", this), new Integer(168));
	literals.put(new ANTLRHashString("initializer", this), new Integer(228));
	literals.put(new ANTLRHashString("synchronized", this), new Integer(51));
	literals.put(new ANTLRHashString("_nowarn", this), new Integer(63));
	literals.put(new ANTLRHashString("model", this), new Integer(242));
	literals.put(new ANTLRHashString("\\nowarn_op", this), new Integer(143));
	literals.put(new ANTLRHashString("case", this), new Integer(9));
	literals.put(new ANTLRHashString("normal_behaviour", this), new Integer(253));
	literals.put(new ANTLRHashString("final", this), new Integer(21));
	literals.put(new ANTLRHashString("\\java_math", this), new Integer(131));
	literals.put(new ANTLRHashString("\\exists", this), new Integer(125));
	literals.put(new ANTLRHashString("code", this), new Integer(190));
	literals.put(new ANTLRHashString("callable_redundantly", this), new Integer(185));
	literals.put(new ANTLRHashString("maintaining_redundantly", this), new Integer(236));
	literals.put(new ANTLRHashString("true", this), new Integer(56));
	literals.put(new ANTLRHashString("code_safe_math", this), new Integer(194));
	literals.put(new ANTLRHashString("\\sum", this), new Integer(160));
	literals.put(new ANTLRHashString("\\old", this), new Integer(145));
	literals.put(new ANTLRHashString("\\invariant_for", this), new Integer(129));
	literals.put(new ANTLRHashString("transient", this), new Integer(55));
	literals.put(new ANTLRHashString("breaks_redundantly", this), new Integer(183));
	literals.put(new ANTLRHashString("do", this), new Integer(16));
	literals.put(new ANTLRHashString("\\bigint_math", this), new Integer(121));
	literals.put(new ANTLRHashString("uninitialized", this), new Integer(286));
	literals.put(new ANTLRHashString("\\min", this), new Integer(136));
	literals.put(new ANTLRHashString("\\bigint", this), new Integer(120));
	literals.put(new ANTLRHashString("implements", this), new Integer(27));
	literals.put(new ANTLRHashString("code_contract", this), new Integer(192));
	literals.put(new ANTLRHashString("resend", this), new Integer(44));
	literals.put(new ANTLRHashString("field", this), new Integer(218));
	literals.put(new ANTLRHashString("set", this), new Integer(275));
	literals.put(new ANTLRHashString("breaks", this), new Integer(182));
	literals.put(new ANTLRHashString("rep", this), new Integer(42));
	literals.put(new ANTLRHashString("protected", this), new Integer(38));
	literals.put(new ANTLRHashString("signals_only", this), new Integer(277));
	literals.put(new ANTLRHashString("or", this), new Integer(258));
	literals.put(new ANTLRHashString("when_redundantly", this), new Integer(290));
	literals.put(new ANTLRHashString("finally", this), new Integer(22));
	literals.put(new ANTLRHashString("char", this), new Integer(11));
	literals.put(new ANTLRHashString("if", this), new Integer(26));
	literals.put(new ANTLRHashString("const", this), new Integer(13));
	literals.put(new ANTLRHashString("\\space", this), new Integer(158));
	literals.put(new ANTLRHashString("requires_redundantly", this), new Integer(271));
	literals.put(new ANTLRHashString("duration", this), new Integer(207));
	literals.put(new ANTLRHashString("return", this), new Integer(45));
	literals.put(new ANTLRHashString("for_example", this), new Integer(220));
	literals.put(new ANTLRHashString("loop_invariant", this), new Integer(233));
	literals.put(new ANTLRHashString("default", this), new Integer(15));
	literals.put(new ANTLRHashString("instanceof", this), new Integer(29));
	literals.put(new ANTLRHashString("captures", this), new Integer(186));
	literals.put(new ANTLRHashString("new", this), new Integer(34));
	literals.put(new ANTLRHashString("native", this), new Integer(33));
	literals.put(new ANTLRHashString("\\peer", this), new Integer(166));
	literals.put(new ANTLRHashString("extract", this), new Integer(217));
	literals.put(new ANTLRHashString("choose", this), new Integer(188));
	literals.put(new ANTLRHashString("ghost", this), new Integer(221));
	literals.put(new ANTLRHashString("ensures", this), new Integer(209));
	literals.put(new ANTLRHashString("measured_by_redundantly", this), new Integer(240));
	literals.put(new ANTLRHashString("post_redundantly", this), new Integer(260));
	literals.put(new ANTLRHashString("assert", this), new Integer(5));
	literals.put(new ANTLRHashString("exceptional_behaviour", this), new Integer(213));
	literals.put(new ANTLRHashString("normal_example", this), new Integer(254));
	literals.put(new ANTLRHashString("represents", this), new Integer(268));
	literals.put(new ANTLRHashString("int", this), new Integer(30));
	literals.put(new ANTLRHashString("constraint", this), new Integer(195));
	literals.put(new ANTLRHashString("nullable", this), new Integer(255));
	literals.put(new ANTLRHashString("_nowarn_op", this), new Integer(64));
	literals.put(new ANTLRHashString("\\duration", this), new Integer(122));
	literals.put(new ANTLRHashString("returns_redundantly", this), new Integer(273));
	literals.put(new ANTLRHashString("initially", this), new Integer(229));
	literals.put(new ANTLRHashString("hence_by", this), new Integer(223));
	literals.put(new ANTLRHashString("assignable", this), new Integer(175));
	literals.put(new ANTLRHashString("goto", this), new Integer(25));
	literals.put(new ANTLRHashString("represents_redundantly", this), new Integer(269));
	literals.put(new ANTLRHashString("axiom", this), new Integer(179));
	literals.put(new ANTLRHashString("code_bigint_math", this), new Integer(191));
	literals.put(new ANTLRHashString("\\real", this), new Integer(154));
	literals.put(new ANTLRHashString("class", this), new Integer(12));
	literals.put(new ANTLRHashString("\\num_of", this), new Integer(144));
	literals.put(new ANTLRHashString("\\fresh", this), new Integer(127));
	literals.put(new ANTLRHashString("writable", this), new Integer(293));
	literals.put(new ANTLRHashString("returns", this), new Integer(272));
	literals.put(new ANTLRHashString("maintaining", this), new Integer(235));
	literals.put(new ANTLRHashString("working_space", this), new Integer(291));
	literals.put(new ANTLRHashString("query", this), new Integer(263));
	literals.put(new ANTLRHashString("old", this), new Integer(257));
	literals.put(new ANTLRHashString("\\TYPE", this), new Integer(119));
	literals.put(new ANTLRHashString("while", this), new Integer(60));
	literals.put(new ANTLRHashString("boolean", this), new Integer(6));
	literals.put(new ANTLRHashString("modifies_redundantly", this), new Integer(247));
	literals.put(new ANTLRHashString("ensures_redundantly", this), new Integer(210));
	literals.put(new ANTLRHashString("exceptional_behavior", this), new Integer(212));
	literals.put(new ANTLRHashString("static_initializer", this), new Integer(285));
	literals.put(new ANTLRHashString("exsures", this), new Integer(215));
	literals.put(new ANTLRHashString("assignable_redundantly", this), new Integer(176));
	literals.put(new ANTLRHashString("package", this), new Integer(36));
	literals.put(new ANTLRHashString("\\everything", this), new Integer(124));
	literals.put(new ANTLRHashString("super", this), new Integer(49));
	literals.put(new ANTLRHashString("continues_redundantly", this), new Integer(199));
	literals.put(new ANTLRHashString("choose_if", this), new Integer(189));
	literals.put(new ANTLRHashString("double", this), new Integer(17));
	literals.put(new ANTLRHashString("accessible", this), new Integer(171));
	literals.put(new ANTLRHashString("exceptional_example", this), new Integer(214));
	literals.put(new ANTLRHashString("\\only_assigned", this), new Integer(146));
	literals.put(new ANTLRHashString("\\is_initialized", this), new Integer(130));
	literals.put(new ANTLRHashString("volatile", this), new Integer(59));
	literals.put(new ANTLRHashString("code_java_math", this), new Integer(193));
	literals.put(new ANTLRHashString("\\only_accessed", this), new Integer(147));
	literals.put(new ANTLRHashString("readable", this), new Integer(264));
	literals.put(new ANTLRHashString("diverges_redundantly", this), new Integer(206));
	literals.put(new ANTLRHashString("monitors_for", this), new Integer(249));
	literals.put(new ANTLRHashString("\\into", this), new Integer(128));
}

public Token nextToken() throws TokenStreamException {
	Token theRetToken=null;
tryAgain:
	for (;;) {
		Token _token = null;
		int _ttype = Token.INVALID_TYPE;
		resetText();
		try {   // for char stream error handling
			try {   // for lexical error handling
				switch ( LA(1)) {
				case '\t':  case '\n':  case '\u000c':  case '\r':
				case ' ':
				{
					mWS(true);
					theRetToken=_returnToken;
					break;
				}
				case ')':
				{
					mRPAREN(true);
					theRetToken=_returnToken;
					break;
				}
				case ';':
				{
					mSEMI(true);
					theRetToken=_returnToken;
					break;
				}
				case '}':
				{
					mRCURLY(true);
					theRetToken=_returnToken;
					break;
				}
				case '$':  case 'A':  case 'B':  case 'C':
				case 'D':  case 'E':  case 'F':  case 'G':
				case 'H':  case 'I':  case 'J':  case 'K':
				case 'L':  case 'M':  case 'N':  case 'O':
				case 'P':  case 'Q':  case 'R':  case 'S':
				case 'T':  case 'U':  case 'V':  case 'W':
				case 'X':  case 'Y':  case 'Z':  case '\\':
				case '_':  case 'a':  case 'b':  case 'c':
				case 'd':  case 'e':  case 'f':  case 'g':
				case 'h':  case 'i':  case 'j':  case 'k':
				case 'l':  case 'm':  case 'n':  case 'o':
				case 'p':  case 'q':  case 'r':  case 's':
				case 't':  case 'u':  case 'v':  case 'w':
				case 'x':  case 'y':  case 'z':
				{
					mIDENT(true);
					theRetToken=_returnToken;
					break;
				}
				case ',':
				{
					mCOMMA(true);
					theRetToken=_returnToken;
					break;
				}
				case '.':  case '0':  case '1':  case '2':
				case '3':  case '4':  case '5':  case '6':
				case '7':  case '8':  case '9':
				{
					mINTEGER_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case '~':
				{
					mBNOT(true);
					theRetToken=_returnToken;
					break;
				}
				case ':':
				{
					mCOLON(true);
					theRetToken=_returnToken;
					break;
				}
				case '[':
				{
					mLBRACK(true);
					theRetToken=_returnToken;
					break;
				}
				case '?':
				{
					mQUESTION(true);
					theRetToken=_returnToken;
					break;
				}
				case ']':
				{
					mRBRACK(true);
					theRetToken=_returnToken;
					break;
				}
				case '\'':
				{
					mCHARACTER_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case '"':
				{
					mSTRING_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				default:
					if (((LA(1)=='<') && (LA(2)=='=') && (LA(3)=='=') && (LA(4)=='>'))&&(inAnnotation)) {
						mEQUIV(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='>') && (LA(2)=='>') && (LA(3)=='>') && (LA(4)=='='))&&(parsingController.getUnmatchedTypeLT()==0)) {
						mBSR_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='*') && (LA(3)=='*')) {
						mJAVADOC_OPEN(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='<') && (LA(2)=='=') && (LA(3)=='!'))&&(inAnnotation)) {
						mNOT_EQUIV(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='=') && (LA(2)=='=') && (LA(3)=='>'))&&(inAnnotation)) {
						mIMPLIES(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='<') && (LA(2)=='=') && (LA(3)=='=') && (true))&&(inAnnotation)) {
						mBACKWARD_IMPLIES(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='*') && (_tokenSet_0.member(LA(3)))) {
						mML_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='>') && (LA(2)=='>') && (LA(3)=='>') && (true))&&(parsingController.getUnmatchedTypeLT()==0)) {
						mBSR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='<') && (LA(2)=='<') && (LA(3)=='=')) {
						mSL_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='>') && (LA(2)=='>') && (LA(3)=='='))&&(parsingController.getUnmatchedTypeLT()==0)) {
						mSR_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='*'||LA(1)=='@') && (_tokenSet_1.member(LA(2)))) {
						mJML_CLOSE(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='(') && (LA(2)=='*')) {
						mINFORMAL_DESC(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='<') && (LA(2)=='-'))&&(inAnnotation)) {
						mL_ARROW(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='-') && (LA(2)=='>'))&&(inAnnotation)) {
						mR_ARROW(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='<') && (LA(2)==':'))&&(inAnnotation)) {
						mSUBTYPE_OF(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='{') && (LA(2)=='|'))&&(inAnnotation)) {
						mLCURLY_VBAR(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='|') && (LA(2)=='}'))&&(inAnnotation)) {
						mVBAR_RCURLY(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='/')) {
						mSL_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='&') && (LA(2)=='=')) {
						mBAND_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (LA(2)=='=')) {
						mBOR_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='^') && (LA(2)=='=')) {
						mBXOR_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (LA(2)=='-')) {
						mDEC(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='=') && (LA(2)=='=') && (true)) {
						mEQUAL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='>') && (LA(2)=='=')) {
						mGE(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='+') && (LA(2)=='+')) {
						mINC(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='&') && (LA(2)=='&')) {
						mLAND(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='<') && (LA(2)=='=') && (true)) {
						mLE(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (LA(2)=='|')) {
						mLOR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (LA(2)=='=')) {
						mMINUS_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='!') && (LA(2)=='=')) {
						mNOT_EQUAL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='%') && (LA(2)=='=')) {
						mPERCENT_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='+') && (LA(2)=='=')) {
						mPLUS_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='<') && (LA(2)=='<') && (true)) {
						mSL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='=')) {
						mSLASH_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if (((LA(1)=='>') && (LA(2)=='>') && (true))&&(parsingController.getUnmatchedTypeLT()==0)) {
						mSR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='*') && (LA(2)=='=')) {
						mSTAR_ASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='+') && (true)) {
						mPLUS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (true)) {
						mMINUS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='*') && (true)) {
						mSTAR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (true)) {
						mSLASH(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='%') && (true)) {
						mPERCENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='(') && (true)) {
						mLPAREN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='{') && (true)) {
						mLCURLY(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='=') && (true)) {
						mASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='@') && (true)) {
						mAT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='&') && (true)) {
						mBAND(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (true)) {
						mBOR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='^') && (true)) {
						mBXOR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='>') && (true)) {
						mGT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='!') && (true)) {
						mLNOT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='<') && (true)) {
						mLT(true);
						theRetToken=_returnToken;
					}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				}
				if ( _returnToken==null ) continue tryAgain; // found SKIP token
				_ttype = _returnToken.getType();
				_returnToken.setType(_ttype);
				return _returnToken;
			}
			catch (RecognitionException e) {
				throw new TokenStreamRecognitionException(e);
			}
		}
		catch (CharStreamException cse) {
			if ( cse instanceof CharStreamIOException ) {
				throw new TokenStreamIOException(((CharStreamIOException)cse).io);
			}
			else {
				throw new TokenStreamException(cse.getMessage());
			}
		}
	}
}

	public final void mPLUS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PLUS;
		int _saveIndex;
		
		match('+');
		if ( inputState.guessing==0 ) {
			CToken t = new CToken(PLUS , new String(text.getBuffer(),_begin,text.length()-_begin), JmlIDKeywords.INSIDE_ANNOTATION);
			_token = t;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mMINUS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MINUS;
		int _saveIndex;
		
		match('-');
		if ( inputState.guessing==0 ) {
			CToken t = new CToken(MINUS , new String(text.getBuffer(),_begin,text.length()-_begin), JmlIDKeywords.INSIDE_ANNOTATION);
			_token = t;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STAR;
		int _saveIndex;
		
		match('*');
		if ( inputState.guessing==0 ) {
			CToken t = new CToken(STAR , new String(text.getBuffer(),_begin,text.length()-_begin), JmlIDKeywords.INSIDE_ANNOTATION);
			_token = t;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSLASH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SLASH;
		int _saveIndex;
		
		match('/');
		if ( inputState.guessing==0 ) {
			CToken t = new CToken(SLASH , new String(text.getBuffer(),_begin,text.length()-_begin), JmlIDKeywords.INSIDE_ANNOTATION);
			_token = t;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPERCENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PERCENT;
		int _saveIndex;
		
		match('%');
		if ( inputState.guessing==0 ) {
			CToken t = new CToken(PERCENT , new String(text.getBuffer(),_begin,text.length()-_begin), JmlIDKeywords.INSIDE_ANNOTATION);
			_token = t;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mWS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = WS;
		int _saveIndex;
		
		{
		boolean synPredMatched12 = false;
		if (((LA(1)=='\n'||LA(1)=='\r') && (_tokenSet_2.member(LA(2))) && (true) && (true))) {
			int _m12 = mark();
			synPredMatched12 = true;
			inputState.guessing++;
			try {
				{
				mNEWLINE(false);
				{
				_loop10:
				do {
					if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
						mNON_NL_WS(false);
					}
					else {
						break _loop10;
					}
					
				} while (true);
				}
				{
				match('@');
				}
				}
			}
			catch (RecognitionException pe) {
				synPredMatched12 = false;
			}
			rewind(_m12);
inputState.guessing--;
		}
		if ( synPredMatched12 ) {
			mNEWLINE(false);
			{
			_loop14:
			do {
				if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
					mNON_NL_WS(false);
				}
				else {
					break _loop14;
				}
				
			} while (true);
			}
			{
			int _cnt16=0;
			_loop16:
			do {
				if ((LA(1)=='@')) {
					match('@');
				}
				else {
					if ( _cnt16>=1 ) { break _loop16; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt16++;
			} while (true);
			}
			{
			if ((LA(1)=='+')) {
				match("+*/");
				if ( inputState.guessing==0 ) {
					
							    // This is a case of JML_CLOSE
							    lexingController.pop(); 
							    lexingController.retry(); 
							
				}
			}
			else {
			}
			
			}
		}
		else if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
			mNON_NL_WS(false);
		}
		else if ((LA(1)=='\n'||LA(1)=='\r') && (true) && (true) && (true)) {
			mNEWLINE(false);
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNON_NL_WS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NON_NL_WS;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case ' ':
		{
			match(' ');
			break;
		}
		case '\t':
		{
			match('\t');
			break;
		}
		case '\u000c':
		{
			match('\f');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNEWLINE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NEWLINE;
		int _saveIndex;
		
		{
		if ((LA(1)=='\r') && (LA(2)=='\n') && (true) && (true)) {
			match('\r');
			match('\n');
		}
		else if ((LA(1)=='\r') && (true) && (true) && (true)) {
			match('\r');
		}
		else if ((LA(1)=='\n')) {
			match('\n');
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		if ( inputState.guessing==0 ) {
			newline();
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mOPTIONAL_PLUS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = OPTIONAL_PLUS;
		int _saveIndex;
		
		{
		if ((LA(1)=='+') && (_tokenSet_0.member(LA(2))) && (true) && (true)) {
			match('+');
		}
		else if ((_tokenSet_0.member(LA(1))) && (true) && (true) && (true)) {
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mJAVADOC_OPEN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = JAVADOC_OPEN;
		int _saveIndex;
		
		{
		if ((LA(1)=='/') && (LA(2)=='*') && (LA(3)=='*') && (LA(4)=='/')) {
			match("/**/");
		}
		else if ((LA(1)=='/') && (LA(2)=='*') && (LA(3)=='*') && (_tokenSet_0.member(LA(4)))) {
			match("/**");
			mML_COMMENT_REST(false);
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mML_COMMENT_REST(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ML_COMMENT_REST;
		int _saveIndex;
		
		mOPTIONAL_PLUS(false);
		{
		if ((_tokenSet_3.member(LA(1)))) {
			{
			if ((LA(1)=='\n'||LA(1)=='\r')) {
				mNEWLINE(false);
			}
			else if ((_tokenSet_4.member(LA(1)))) {
				{
				match(_tokenSet_4);
				}
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			
			}
			{
			_loop76:
			do {
				if (((LA(1)=='*') && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0000' && LA(3) <= '\u00ff')))&&( LA(2)!='/' )) {
					match('*');
				}
				else if ((LA(1)=='\n'||LA(1)=='\r')) {
					mNEWLINE(false);
				}
				else if ((_tokenSet_5.member(LA(1)))) {
					{
					match(_tokenSet_5);
					}
				}
				else {
					break _loop76;
				}
				
			} while (true);
			}
			match("*/");
			if ( inputState.guessing==0 ) {
				_ttype = Token.SKIP;
			}
		}
		else if ((LA(1)=='@')) {
			match('@');
			{
			_loop78:
			do {
				if ((LA(1)=='@')) {
					match('@');
				}
				else {
					break _loop78;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
						try {
						    if (!allowAnnotations) {
							throw new TokenStreamException(
							    new Message( JmlMessages.NESTED_ANNOTATION ).
							    getMessage()
							);
						    }
						    lexingController.push("jmlML");
						} catch( IllegalArgumentException e ) {
						    throw
						    new TokenStreamException( "No JML lexer available." );
						}
						lexingController.retry();
					
			}
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mML_EMPTY_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ML_EMPTY_COMMENT;
		int _saveIndex;
		
		match("/**/");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mJML_CLOSE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = JML_CLOSE;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case '@':
		{
			{
			int _cnt26=0;
			_loop26:
			do {
				if ((LA(1)=='@')) {
					match('@');
				}
				else {
					if ( _cnt26>=1 ) { break _loop26; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt26++;
			} while (true);
			}
			{
			switch ( LA(1)) {
			case '+':
			{
				match('+');
				break;
			}
			case '*':
			{
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			break;
		}
		case '*':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		match("*/");
		if ( inputState.guessing==0 ) {
			
				    lexingController.pop(); 
				    lexingController.retry(); 
				
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mINFORMAL_DESC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = INFORMAL_DESC;
		int _saveIndex;
		
		{
		_saveIndex=text.length();
		match("(*");
		text.setLength(_saveIndex);
		{
		_loop31:
		do {
			if (((LA(1)=='*') && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0000' && LA(3) <= '\u00ff')) && (true))&&(LA(2) != ')')) {
				_saveIndex=text.length();
				match('*');
				text.setLength(_saveIndex);
			}
			else {
				break _loop31;
			}
			
		} while (true);
		}
		}
		{
		_loop39:
		do {
			if (((LA(1)=='*') && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0000' && LA(3) <= '\u00ff')))&&( LA(2)!=')' )) {
				match('*');
			}
			else if ((_tokenSet_5.member(LA(1)))) {
				{
				match(_tokenSet_5);
				}
			}
			else if ((LA(1)=='\n'||LA(1)=='\r')) {
				_saveIndex=text.length();
				mNEWLINE(false);
				text.setLength(_saveIndex);
				{
				{
				_loop36:
				do {
					if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ') && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0000' && LA(3) <= '\u00ff')) && (true)) {
						_saveIndex=text.length();
						mNON_NL_WS(false);
						text.setLength(_saveIndex);
					}
					else {
						break _loop36;
					}
					
				} while (true);
				}
				{
				_loop38:
				do {
					if ((LA(1)=='@') && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && ((LA(3) >= '\u0000' && LA(3) <= '\u00ff')) && (true)) {
						_saveIndex=text.length();
						match('@');
						text.setLength(_saveIndex);
					}
					else {
						break _loop38;
					}
					
				} while (true);
				}
				}
			}
			else {
				break _loop39;
			}
			
		} while (true);
		}
		_saveIndex=text.length();
		match("*)");
		text.setLength(_saveIndex);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LPAREN;
		int _saveIndex;
		
		match('(');
		if ( inputState.guessing==0 ) {
			lexingController.lexedLeftParen();
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RPAREN;
		int _saveIndex;
		
		match(')');
		if ( inputState.guessing==0 ) {
			lexingController.lexedRightParen();
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSEMI(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SEMI;
		int _saveIndex;
		
		match(';');
		if ( inputState.guessing==0 ) {
			lexingController.lexedSemicolon();
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLCURLY(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LCURLY;
		int _saveIndex;
		
		match('{');
		if ( inputState.guessing==0 ) {
			lexingController.lexedLCurly();
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRCURLY(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RCURLY;
		int _saveIndex;
		
		match('}');
		if ( inputState.guessing==0 ) {
			Token t = makeToken(_ttype); _token = t; lexingController.lexedRCurly(t);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mL_ARROW(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = L_ARROW;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("<-");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mR_ARROW(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = R_ARROW;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("->");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEQUIV(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EQUIV;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("<==>");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNOT_EQUIV(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOT_EQUIV;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("<=!=>");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mIMPLIES(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IMPLIES;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("==>");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBACKWARD_IMPLIES(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BACKWARD_IMPLIES;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("<==");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSUBTYPE_OF(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SUBTYPE_OF;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("<:");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLCURLY_VBAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LCURLY_VBAR;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("{|");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mVBAR_RCURLY(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = VBAR_RCURLY;
		int _saveIndex;
		
		if (!(inAnnotation))
		  throw new SemanticException("inAnnotation");
		match("|}");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSL_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SL_COMMENT;
		int _saveIndex;
		
		match("//");
		{
		if ((LA(1)=='+') && (_tokenSet_6.member(LA(2)))) {
			match('+');
			{
			match(_tokenSet_6);
			}
			{
			_loop65:
			do {
				if ((_tokenSet_7.member(LA(1)))) {
					{
					match(_tokenSet_7);
					}
				}
				else {
					break _loop65;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
						_ttype = Token.SKIP;
					
			}
		}
		else if (((LA(1)=='+') && (true) && (true) && (true))&&( LA(2)=='\n' || LA(2)=='\r' )) {
			match('+');
			if ( inputState.guessing==0 ) {
				
						_ttype = Token.SKIP;
					
			}
		}
		else if ((_tokenSet_8.member(LA(1)))) {
			{
			match(_tokenSet_8);
			}
			{
			_loop61:
			do {
				if ((_tokenSet_7.member(LA(1)))) {
					{
					match(_tokenSet_7);
					}
				}
				else {
					break _loop61;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
						_ttype = Token.SKIP;
					
			}
		}
		else if ((LA(1)=='+'||LA(1)=='@') && (true) && (true) && (true)) {
			{
			switch ( LA(1)) {
			case '+':
			{
				match('+');
				break;
			}
			case '@':
			{
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			match('@');
			{
			_loop68:
			do {
				if ((LA(1)=='@')) {
					match('@');
				}
				else {
					break _loop68;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
						if (!allowAnnotations) {
						    // If we are in an annotation, we allow a single-line
						    // annotation - just ignore the initial token and
						    // continue on in annotation mode.
						    _ttype = Token.SKIP;
						} else {
				
						    try {
							if (!allowAnnotations) {
							    //  						throw new TokenStreamException(
							    //  							new Message( JmlMessages.NESTED_ANNOTATION ).
							    //  							getMessage()
							    //  						);
							    // If we are in an annotation, we allow a single-line
							    // annotation - just ignore the initial token and
							    // continue on in annotation mode.
							    _ttype = Token.SKIP;
							} else {
							    lexingController.push("jmlSL");
							}
						    } catch( IllegalArgumentException e ) {
							throw
							new TokenStreamException(
							    "No single-line JML lexer available." );
						    }
						    lexingController.retry();
				
						}
					
			}
		}
		else {
			boolean synPredMatched57 = false;
			if (( true )) {
				int _m57 = mark();
				synPredMatched57 = true;
				inputState.guessing++;
				try {
					{
					mNEWLINE(false);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched57 = false;
				}
				rewind(_m57);
inputState.guessing--;
			}
			if ( synPredMatched57 ) {
				if ( inputState.guessing==0 ) {
					
							_ttype = Token.SKIP;
						
				}
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
				_token = makeToken(_ttype);
				_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
			}
			_returnToken = _token;
		}
		
	public final void mML_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ML_COMMENT;
		int _saveIndex;
		
		match("/*");
		mML_COMMENT_REST(false);
		if ( inputState.guessing==0 ) {
			_ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mIDENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IDENT;
		int _saveIndex;
		
		{
		if (((LA(1)=='\\'))&&(inAnnotation)) {
			match('\\');
		}
		else if ((_tokenSet_9.member(LA(1)))) {
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		{
		switch ( LA(1)) {
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':  case 'g':  case 'h':
		case 'i':  case 'j':  case 'k':  case 'l':
		case 'm':  case 'n':  case 'o':  case 'p':
		case 'q':  case 'r':  case 's':  case 't':
		case 'u':  case 'v':  case 'w':  case 'x':
		case 'y':  case 'z':
		{
			matchRange('a','z');
			break;
		}
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':
		{
			matchRange('A','Z');
			break;
		}
		case '_':
		{
			match('_');
			break;
		}
		case '$':
		{
			match('$');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		{
		_loop83:
		do {
			switch ( LA(1)) {
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':  case 'g':  case 'h':
			case 'i':  case 'j':  case 'k':  case 'l':
			case 'm':  case 'n':  case 'o':  case 'p':
			case 'q':  case 'r':  case 's':  case 't':
			case 'u':  case 'v':  case 'w':  case 'x':
			case 'y':  case 'z':
			{
				matchRange('a','z');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':
			{
				matchRange('A','Z');
				break;
			}
			case '_':
			{
				match('_');
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				matchRange('0','9');
				break;
			}
			case '$':
			{
				match('$');
				break;
			}
			default:
			{
				break _loop83;
			}
			}
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    String stext = new String(text.getBuffer(),_begin,text.length()-_begin);
				    int tokenLen = stext.length();
				    if( charCache == null || charCache.length < tokenLen ) {
					charCache = stext.toCharArray();
				    } else {
					stext.getChars( 0, tokenLen, charCache, 0 );
				    }
				    if (stext.equals("nowarn") && inAnnotation) {
					//System.out.println("NOWARN ON LINE " + getLine() );
					// For now, we just ignore the nowarn annotations;
					// eventually we want to remember the warning type and
					// filter logical (not parsing or typechecking) warnings
					// that are found. (!FIXME! someday - DRCok)
					_ttype = Token.SKIP;
					ArrayList list = new ArrayList();
					mNOWARN_LABEL_LIST(false,list);
					//System.out.print("Nowarn at " + getFilename() + " " + getLine());
					//for (int i=0; i<list.size(); ++i) System.out.print(" " + (String)(list.elementAt(i)));
					//System.out.println("");
				    } else {
			
			Token tok;
			if( inAnnotation ) {
			tok = lexingController.lookupJMLToken( charCache, 0,
			tokenLen );
			} else {
			tok = JmlTopIDKeywords.lookup( charCache, 0, tokenLen );
			}
			
					tok = checkReservedTokens( tok );
			
			if( tok == null ) {
			if (charCache[0] == '\\') {
			// We don't allow identifiers to start with '\'.  If we
			// failed to find a keyword, then the leading '\' here
			// is an error.
			// To get this error to go away after adding a
			// new \whatever expression form to JML, you
			// need to edit the file JmlExprID.t
			throw new TokenStreamException( "unexpected char: \\" );
			}
			tok = CToken.lookupToken( MjcTokenTypes.IDENT,
			charCache, 0, tokenLen );
			}
			
			tok.setLine( getLine() );
			tok.setColumn( getColumn() );
			_token =  tok;
			
				    }
				
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNOWARN_LABEL_LIST(boolean _createToken,
		ArrayList list
	) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOWARN_LABEL_LIST;
		int _saveIndex;
		Token t=null;
		Token tt=null;
		
		{
		_loop86:
		do {
			if ((_tokenSet_10.member(LA(1)))) {
				mWS(false);
			}
			else {
				break _loop86;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case '$':  case 'A':  case 'B':  case 'C':
		case 'D':  case 'E':  case 'F':  case 'G':
		case 'H':  case 'I':  case 'J':  case 'K':
		case 'L':  case 'M':  case 'N':  case 'O':
		case 'P':  case 'Q':  case 'R':  case 'S':
		case 'T':  case 'U':  case 'V':  case 'W':
		case 'X':  case 'Y':  case 'Z':  case '_':
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':  case 'g':  case 'h':
		case 'i':  case 'j':  case 'k':  case 'l':
		case 'm':  case 'n':  case 'o':  case 'p':
		case 'q':  case 'r':  case 's':  case 't':
		case 'u':  case 'v':  case 'w':  case 'x':
		case 'y':  case 'z':
		{
			mNOWARN_LABEL(true);
			t=_returnToken;
			if ( inputState.guessing==0 ) {
				list.add(t.getText());
			}
			{
			_loop89:
			do {
				if ((_tokenSet_10.member(LA(1)))) {
					mWS(false);
				}
				else {
					break _loop89;
				}
				
			} while (true);
			}
			{
			_loop95:
			do {
				if ((LA(1)==',')) {
					mCOMMA(false);
					{
					_loop92:
					do {
						if ((_tokenSet_10.member(LA(1)))) {
							mWS(false);
						}
						else {
							break _loop92;
						}
						
					} while (true);
					}
					mNOWARN_LABEL(true);
					tt=_returnToken;
					if ( inputState.guessing==0 ) {
						list.add(tt.getText());
					}
					{
					_loop94:
					do {
						if ((_tokenSet_10.member(LA(1)))) {
							mWS(false);
						}
						else {
							break _loop94;
						}
						
					} while (true);
					}
				}
				else {
					break _loop95;
				}
				
			} while (true);
			}
			break;
		}
		case ';':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		mSEMI(false);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNOWARN_LABEL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOWARN_LABEL;
		int _saveIndex;
		
		{
		int _cnt98=0;
		_loop98:
		do {
			switch ( LA(1)) {
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':  case 'g':  case 'h':
			case 'i':  case 'j':  case 'k':  case 'l':
			case 'm':  case 'n':  case 'o':  case 'p':
			case 'q':  case 'r':  case 's':  case 't':
			case 'u':  case 'v':  case 'w':  case 'x':
			case 'y':  case 'z':
			{
				matchRange('a','z');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':
			{
				matchRange('A','Z');
				break;
			}
			case '_':
			{
				match('_');
				break;
			}
			case '$':
			{
				match('$');
				break;
			}
			default:
			{
				if ( _cnt98>=1 ) { break _loop98; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
			}
			}
			_cnt98++;
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOMMA(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COMMA;
		int _saveIndex;
		
		match(',');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mSKIP_TO_SEMI(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SKIP_TO_SEMI;
		int _saveIndex;
		
		{
		_loop102:
		do {
			if ((_tokenSet_11.member(LA(1)))) {
				{
				match(_tokenSet_11);
				}
			}
			else {
				break _loop102;
			}
			
		} while (true);
		}
		mSEMI(false);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mINTEGER_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = INTEGER_LITERAL;
		int _saveIndex;
		boolean isDecimal=false;
		
		switch ( LA(1)) {
		case '.':
		{
			match('.');
			if ( inputState.guessing==0 ) {
				_ttype = DOT;
			}
			{
			if (((LA(1) >= '0' && LA(1) <= '9'))) {
				{
				int _cnt106=0;
				_loop106:
				do {
					if (((LA(1) >= '0' && LA(1) <= '9'))) {
						matchRange('0','9');
					}
					else {
						if ( _cnt106>=1 ) { break _loop106; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
					}
					
					_cnt106++;
				} while (true);
				}
				{
				if ((LA(1)=='E'||LA(1)=='e')) {
					mEXPONENT(false);
				}
				else {
				}
				
				}
				{
				if ((_tokenSet_12.member(LA(1)))) {
					mFLOAT_SUFFIX(false);
				}
				else {
				}
				
				}
				if ( inputState.guessing==0 ) {
					_ttype = REAL_LITERAL;
				}
			}
			else if (((LA(1)=='.'))&&(inAnnotation)) {
				match('.');
				if ( inputState.guessing==0 ) {
					_ttype = DOT_DOT;
				}
			}
			else {
			}
			
			}
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			{
			switch ( LA(1)) {
			case '0':
			{
				match('0');
				if ( inputState.guessing==0 ) {
					isDecimal = true;
				}
				{
				switch ( LA(1)) {
				case 'X':  case 'x':
				{
					{
					switch ( LA(1)) {
					case 'x':
					{
						match('x');
						break;
					}
					case 'X':
					{
						match('X');
						break;
					}
					default:
					{
						throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
					}
					}
					}
					{
					int _cnt113=0;
					_loop113:
					do {
						if ((_tokenSet_13.member(LA(1))) && (true) && (true) && (true)) {
							mHEX_DIGIT(false);
						}
						else {
							if ( _cnt113>=1 ) { break _loop113; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
						}
						
						_cnt113++;
					} while (true);
					}
					break;
				}
				case '0':  case '1':  case '2':  case '3':
				case '4':  case '5':  case '6':  case '7':
				{
					{
					int _cnt115=0;
					_loop115:
					do {
						if (((LA(1) >= '0' && LA(1) <= '7'))) {
							matchRange('0','7');
						}
						else {
							if ( _cnt115>=1 ) { break _loop115; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
						}
						
						_cnt115++;
					} while (true);
					}
					break;
				}
				default:
					{
					}
				}
				}
				break;
			}
			case '1':  case '2':  case '3':  case '4':
			case '5':  case '6':  case '7':  case '8':
			case '9':
			{
				{
				matchRange('1','9');
				}
				{
				_loop118:
				do {
					if (((LA(1) >= '0' && LA(1) <= '9'))) {
						matchRange('0','9');
					}
					else {
						break _loop118;
					}
					
				} while (true);
				}
				if ( inputState.guessing==0 ) {
					isDecimal=true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			{
			if ((LA(1)=='L'||LA(1)=='l')) {
				{
				switch ( LA(1)) {
				case 'l':
				{
					match('l');
					break;
				}
				case 'L':
				{
					match('L');
					break;
				}
				default:
				{
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
				}
			}
			else if (((_tokenSet_14.member(LA(1))))&&(isDecimal && !(LA(1)=='.' && LA(2)=='.'))) {
				{
				switch ( LA(1)) {
				case '.':
				{
					match('.');
					{
					_loop123:
					do {
						if (((LA(1) >= '0' && LA(1) <= '9'))) {
							matchRange('0','9');
						}
						else {
							break _loop123;
						}
						
					} while (true);
					}
					{
					if ((LA(1)=='E'||LA(1)=='e')) {
						mEXPONENT(false);
					}
					else {
					}
					
					}
					{
					if ((_tokenSet_12.member(LA(1)))) {
						mFLOAT_SUFFIX(false);
					}
					else {
					}
					
					}
					break;
				}
				case 'E':  case 'e':
				{
					mEXPONENT(false);
					{
					if ((_tokenSet_12.member(LA(1)))) {
						mFLOAT_SUFFIX(false);
					}
					else {
					}
					
					}
					break;
				}
				case 'D':  case 'F':  case 'd':  case 'f':
				{
					mFLOAT_SUFFIX(false);
					break;
				}
				default:
				{
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					_ttype = REAL_LITERAL;
				}
			}
			else {
			}
			
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mEXPONENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EXPONENT;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case 'e':
		{
			match('e');
			break;
		}
		case 'E':
		{
			match('E');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		{
		switch ( LA(1)) {
		case '+':
		{
			match('+');
			break;
		}
		case '-':
		{
			match('-');
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		{
		int _cnt191=0;
		_loop191:
		do {
			if (((LA(1) >= '0' && LA(1) <= '9'))) {
				matchRange('0','9');
			}
			else {
				if ( _cnt191>=1 ) { break _loop191; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
			}
			
			_cnt191++;
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mFLOAT_SUFFIX(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = FLOAT_SUFFIX;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'f':
		{
			match('f');
			break;
		}
		case 'F':
		{
			match('F');
			break;
		}
		case 'd':
		{
			match('d');
			break;
		}
		case 'D':
		{
			match('D');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mHEX_DIGIT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = HEX_DIGIT;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case '0':  case '1':  case '2':  case '3':
		case '4':  case '5':  case '6':  case '7':
		case '8':  case '9':
		{
			matchRange('0','9');
			break;
		}
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':
		{
			matchRange('A','F');
			break;
		}
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':
		{
			matchRange('a','f');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ASSIGN;
		int _saveIndex;
		
		match('=');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mAT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = AT;
		int _saveIndex;
		
		match('@');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBAND(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BAND;
		int _saveIndex;
		
		match('&');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBAND_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BAND_ASSIGN;
		int _saveIndex;
		
		match("&=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBNOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BNOT;
		int _saveIndex;
		
		match('~');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBOR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BOR;
		int _saveIndex;
		
		match('|');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBOR_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BOR_ASSIGN;
		int _saveIndex;
		
		match("|=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBSR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BSR;
		int _saveIndex;
		
		if (!(parsingController.getUnmatchedTypeLT()==0))
		  throw new SemanticException("parsingController.getUnmatchedTypeLT()==0");
		match(">>>");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBSR_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BSR_ASSIGN;
		int _saveIndex;
		
		if (!(parsingController.getUnmatchedTypeLT()==0))
		  throw new SemanticException("parsingController.getUnmatchedTypeLT()==0");
		match(">>>=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBXOR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BXOR;
		int _saveIndex;
		
		match('^');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBXOR_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BXOR_ASSIGN;
		int _saveIndex;
		
		match("^=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COLON;
		int _saveIndex;
		
		match(':');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDEC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DEC;
		int _saveIndex;
		
		match("--");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEQUAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EQUAL;
		int _saveIndex;
		
		match("==");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mGE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = GE;
		int _saveIndex;
		
		match(">=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mGT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = GT;
		int _saveIndex;
		
		match(">");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mINC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = INC;
		int _saveIndex;
		
		match("++");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLAND(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LAND;
		int _saveIndex;
		
		match("&&");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLBRACK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LBRACK;
		int _saveIndex;
		
		match('[');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LE;
		int _saveIndex;
		
		match("<=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLNOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LNOT;
		int _saveIndex;
		
		match('!');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLOR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LOR;
		int _saveIndex;
		
		match("||");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LT;
		int _saveIndex;
		
		match('<');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mMINUS_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MINUS_ASSIGN;
		int _saveIndex;
		
		match("-=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNOT_EQUAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOT_EQUAL;
		int _saveIndex;
		
		match("!=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPERCENT_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PERCENT_ASSIGN;
		int _saveIndex;
		
		match("%=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPLUS_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PLUS_ASSIGN;
		int _saveIndex;
		
		match("+=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mQUESTION(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = QUESTION;
		int _saveIndex;
		
		match('?');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRBRACK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RBRACK;
		int _saveIndex;
		
		match(']');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SL;
		int _saveIndex;
		
		match("<<");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSLASH_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SLASH_ASSIGN;
		int _saveIndex;
		
		match("/=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSL_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SL_ASSIGN;
		int _saveIndex;
		
		match("<<=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SR;
		int _saveIndex;
		
		if (!(parsingController.getUnmatchedTypeLT()==0))
		  throw new SemanticException("parsingController.getUnmatchedTypeLT()==0");
		match(">>");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSR_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SR_ASSIGN;
		int _saveIndex;
		
		if (!(parsingController.getUnmatchedTypeLT()==0))
		  throw new SemanticException("parsingController.getUnmatchedTypeLT()==0");
		match(">>=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTAR_ASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STAR_ASSIGN;
		int _saveIndex;
		
		match("*=");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCHARACTER_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = CHARACTER_LITERAL;
		int _saveIndex;
		
		_saveIndex=text.length();
		match('\'');
		text.setLength(_saveIndex);
		{
		if ((LA(1)=='\\')) {
			mESC(false);
		}
		else if ((_tokenSet_15.member(LA(1)))) {
			matchNot('\'');
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		_saveIndex=text.length();
		match('\'');
		text.setLength(_saveIndex);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mESC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ESC;
		int _saveIndex;
		
		match('\\');
		{
		switch ( LA(1)) {
		case 'n':
		{
			match('n');
			break;
		}
		case 'r':
		{
			match('r');
			break;
		}
		case 't':
		{
			match('t');
			break;
		}
		case 'b':
		{
			match('b');
			break;
		}
		case 'f':
		{
			match('f');
			break;
		}
		case '"':
		{
			match('"');
			break;
		}
		case '\'':
		{
			match('\'');
			break;
		}
		case '\\':
		{
			match('\\');
			break;
		}
		case 'u':
		{
			{
			int _cnt176=0;
			_loop176:
			do {
				if ((LA(1)=='u')) {
					match('u');
				}
				else {
					if ( _cnt176>=1 ) { break _loop176; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt176++;
			} while (true);
			}
			mHEX_DIGIT(false);
			mHEX_DIGIT(false);
			mHEX_DIGIT(false);
			mHEX_DIGIT(false);
			break;
		}
		case '0':  case '1':  case '2':  case '3':
		{
			{
			matchRange('0','3');
			}
			{
			if (((LA(1) >= '0' && LA(1) <= '7')) && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && (true) && (true)) {
				{
				matchRange('0','7');
				}
				{
				if (((LA(1) >= '0' && LA(1) <= '7')) && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && (true) && (true)) {
					matchRange('0','7');
				}
				else if (((LA(1) >= '\u0000' && LA(1) <= '\u00ff')) && (true) && (true) && (true)) {
				}
				else {
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				
				}
			}
			else if (((LA(1) >= '\u0000' && LA(1) <= '\u00ff')) && (true) && (true) && (true)) {
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			
			}
			break;
		}
		case '4':  case '5':  case '6':  case '7':
		{
			{
			matchRange('4','7');
			}
			{
			if (((LA(1) >= '0' && LA(1) <= '9')) && ((LA(2) >= '\u0000' && LA(2) <= '\u00ff')) && (true) && (true)) {
				{
				matchRange('0','9');
				}
			}
			else if (((LA(1) >= '\u0000' && LA(1) <= '\u00ff')) && (true) && (true) && (true)) {
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTRING_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STRING_LITERAL;
		int _saveIndex;
		
		_saveIndex=text.length();
		match('"');
		text.setLength(_saveIndex);
		{
		_loop172:
		do {
			if ((LA(1)=='\\')) {
				mESC(false);
			}
			else if ((_tokenSet_16.member(LA(1)))) {
				{
				match(_tokenSet_16);
				}
			}
			else {
				break _loop172;
			}
			
		} while (true);
		}
		_saveIndex=text.length();
		match('"');
		text.setLength(_saveIndex);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mVOCAB(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = VOCAB;
		int _saveIndex;
		
		matchRange('\3','\377');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	
	private static final long[] mk_tokenSet_0() {
		long[] data = new long[8];
		data[0]=-4398046511105L;
		for (int i = 1; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 153931627888640L, 1L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 4294972928L, 1L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = new long[8];
		data[0]=-4398046511105L;
		data[1]=-2L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = new long[8];
		data[0]=-4398046520321L;
		data[1]=-2L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = new long[8];
		data[0]=-4398046520321L;
		for (int i = 1; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = new long[8];
		data[0]=-9217L;
		data[1]=-2L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = new long[8];
		data[0]=-9217L;
		for (int i = 1; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = new long[8];
		data[0]=-8796093031425L;
		data[1]=-2L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = { 68719476736L, 576460745995190270L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = { 4294981120L, 0L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = new long[8];
		data[0]=-576460752303423489L;
		for (int i = 1; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = { 0L, 343597383760L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 287948901175001088L, 541165879422L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = { 70368744177664L, 481036337264L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = new long[8];
		data[0]=-549755813889L;
		data[1]=-268435457L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = new long[8];
		data[0]=-17179869185L;
		data[1]=-268435457L;
		for (int i = 2; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	
	}
