// $ANTLR 2.7.7 (20070227): "JavadocJml.g" -> "JavadocJmlLexer.java"$
 
/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1998, 1999 Iowa State University as part of the JML project.
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
 * $Id: JavadocJml.g,v 1.10 2005/01/08 15:11:07 davidcok Exp $
 */

/*
 * These grammars handle the parsing and lexing of javadoc
 * documentation comments.  */

	// common header for lexer and parser
	
	package org.jmlspecs.checker; 
	import java.io.InputStream;
import java.io.Reader;
import java.util.Hashtable;

import org.multijava.mjc.ParsingController;

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
// class preamble for the lexer
	

public class JavadocJmlLexer extends antlr.CharScanner implements JavadocJmlLexerTokenTypes, TokenStream
 {

	final private String eol = System.getProperty("line.separator");

	public JavadocJmlLexer( ParsingController parsingController ) {
		this( parsingController.sharedInputState() );
		this.parsingController = parsingController;
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
	 * Used to switch lexers.  Aliases should be established in all
	 * lexers that share the same input stream. */
	private ParsingController parsingController;

	/**
	 * Used to convert token text from String to char[]. */
	private char[] charCache = null;
public JavadocJmlLexer(InputStream in) {
	this(new ByteBuffer(in));
}
public JavadocJmlLexer(Reader in) {
	this(new CharBuffer(in));
}
public JavadocJmlLexer(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public JavadocJmlLexer(LexerSharedInputState state) {
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
				if ((LA(1)=='<') && (_tokenSet_0.member(LA(2))) && (_tokenSet_1.member(LA(3)))) {
					mEMBEDDED_JML_START(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='*') && (LA(2)=='/')) {
					mJAVADOC_CLOSE(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='\n'||LA(1)=='\r')) {
					mDOC_NL_WS(true);
					theRetToken=_returnToken;
				}
				else if (((_tokenSet_2.member(LA(1))) && (true) && (true))&&( !(LA(1) == '<' && LA(5) == '>' && (
		( LA(2) == 'e' && LA(3) == 's' && LA(4) == 'c') ||
		( LA(2) == 'E' && LA(3) == 'S' && LA(4) == 'C') ||
		( LA(2) == 'j' && LA(3) == 'm' && LA(4) == 'l') ||
		( LA(2) == 'J' && LA(3) == 'M' && LA(4) == 'L'))) )) {
					mREST_OF_LINE(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='*') && (true)) {
					mSTAR(true);
					theRetToken=_returnToken;
				}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
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

	public final void mDOC_NL_WS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_NL_WS;
		int _saveIndex;
		
		mNEWLINE(false);
		{
		mNON_NL_WS_OPT(false);
		}
		{
		_loop11:
		do {
			if (((LA(1)=='*'))&&(LA(2) != '/')) {
				match('*');
			}
			else {
				break _loop11;
			}
			
		} while (true);
		}
		_ttype = Token.SKIP;
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
		if ((LA(1)=='\r') && (LA(2)=='\n')) {
			match('\r');
			match('\n');
		}
		else if ((LA(1)=='\r') && (true)) {
			match('\r');
		}
		else if ((LA(1)=='\n')) {
			match('\n');
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		newline();
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNON_NL_WS_OPT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NON_NL_WS_OPT;
		int _saveIndex;
		
		{
		_loop16:
		do {
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
				break _loop16;
			}
			}
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mREST_OF_LINE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = REST_OF_LINE;
		int _saveIndex;
		
		if (!( !(LA(1) == '<' && LA(5) == '>' && (
		( LA(2) == 'e' && LA(3) == 's' && LA(4) == 'c') ||
		( LA(2) == 'E' && LA(3) == 'S' && LA(4) == 'C') ||
		( LA(2) == 'j' && LA(3) == 'm' && LA(4) == 'l') ||
		( LA(2) == 'J' && LA(3) == 'M' && LA(4) == 'L'))) ))
		  throw new SemanticException(" !(LA(1) == '<' && LA(5) == '>' && (\r\n\t\t( LA(2) == 'e' && LA(3) == 's' && LA(4) == 'c') ||\r\n\t\t( LA(2) == 'E' && LA(3) == 'S' && LA(4) == 'C') ||\r\n\t\t( LA(2) == 'j' && LA(3) == 'm' && LA(4) == 'l') ||\r\n\t\t( LA(2) == 'J' && LA(3) == 'M' && LA(4) == 'L'))) ");
		{
		match(_tokenSet_2);
		}
		{
		_loop21:
		do {
			if (((LA(1)=='*'))&&(LA(2) != '/')) {
				match('*');
			}
			else if (((_tokenSet_2.member(LA(1))))&&( !(LA(1) == '<' && LA(5) == '>' && (
			( LA(2) == 'e' && LA(3) == 's' && LA(4) == 'c') ||
			( LA(2) == 'E' && LA(3) == 'S' && LA(4) == 'C') ||
			( LA(2) == 'j' && LA(3) == 'm' && LA(4) == 'l') ||
			( LA(2) == 'J' && LA(3) == 'M' && LA(4) == 'L'))) )) {
				{
				match(_tokenSet_2);
				}
			}
			else {
				break _loop21;
			}
			
		} while (true);
		}
		if (LA(1)=='\n' || LA(1) == '\r') text.append(eol);
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
		
		match("*");
		_ttype = Token.SKIP;
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mJAVADOC_CLOSE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = JAVADOC_CLOSE;
		int _saveIndex;
		
		match("*/");
		
					parsingController.pop(); 
		
				
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEMBEDDED_JML_START(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EMBEDDED_JML_START;
		int _saveIndex;
		
		match("<");
		{
		switch ( LA(1)) {
		case 'j':
		{
			match("jml");
			break;
		}
		case 'J':
		{
			match("JML");
			break;
		}
		case 'e':
		{
			match("esc");
			break;
		}
		case 'E':
		{
			match("ESC");
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		match(">");
		
					text.setLength(_begin); text.append("");
		
					// quit Javadoc
		
					try {
						parsingController.pop();
					} catch (Exception e) {
						System.out.println(e);
					}
		
					// Start JmlJD
		
					try {
		
						TokenStreamSelector lc = 
						(TokenStreamSelector) (parsingController.get("jml"));
						lc.push("jmlJD");
					} catch( Exception e ) {
						throw 
						new TokenStreamException( "No JmlJD lexer available." + e);
					}
		
				
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 0L, 4535485465632L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 0L, 2286984186306560L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = new long[8];
		data[0]=-4398046520328L;
		for (int i = 1; i<=3; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	
	}
