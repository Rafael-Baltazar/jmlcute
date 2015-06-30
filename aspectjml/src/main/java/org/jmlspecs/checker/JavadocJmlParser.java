// $ANTLR 2.7.7 (20070227): "JavadocJml.g" -> "JavadocJmlParser.java"$
 
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
	import org.multijava.javadoc.JavadocComment;

import antlr.NoViableAltException;
import antlr.ParserSharedInputState;
import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenBuffer;
import antlr.TokenStream;
import antlr.TokenStreamException;
// class preamble for the parser
	

public class JavadocJmlParser extends antlr.LLkParser       implements JavadocJmlTokenTypes
 {


protected JavadocJmlParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public JavadocJmlParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected JavadocJmlParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public JavadocJmlParser(TokenStream lexer) {
  this(lexer,2);
}

public JavadocJmlParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
}

	public final JavadocComment  docComment(
		
	) throws RecognitionException, TokenStreamException {
		JavadocComment self = null;
		
		
			String desc = null;
			StringBuffer fullDescription = null;
		
		
		{
		_loop6:
		do {
			if (((LA(1) >= JAVADOC_CLOSE && LA(1) <= REST_OF_LINE))) {
				{
				_loop4:
				do {
					if ((LA(1)==REST_OF_LINE)) {
						desc=description();
						
								    if( fullDescription == null ) {
									    //desc = desc.trim() + '\n'; // Only needed to match the official version of javadoc pages
									    fullDescription = new StringBuffer( desc );
								    } else {
									    fullDescription.append( desc );
								    }
								
					}
					else {
						break _loop4;
					}
					
				} while (true);
				}
				{
				switch ( LA(1)) {
				case JAVADOC_CLOSE:
				{
					match(JAVADOC_CLOSE);
					
							    if (fullDescription != null) {
								int j = fullDescription.length()-1;
								while (j>=0 && fullDescription.charAt(j)=='*') --j;
							        fullDescription.setLength(j+1);
								char c = fullDescription.charAt(j);
								if (c != '\n' && c != '\r')
					fullDescription.append("\n");
					
							    }
							    JavadocComment next = new JavadocComment( 
									    fullDescription == null ? 
									    "" : fullDescription.toString() );
							    self = self == null ? next : self.add( next );
							    fullDescription = null;
							
					break;
				}
				case EMBEDDED_JML_START:
				{
					match(EMBEDDED_JML_START);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
			}
			else {
				break _loop6;
			}
			
		} while (true);
		}
		match(Token.EOF_TYPE);
		return self;
	}
	
	public final String  description(
		
	) throws RecognitionException, TokenStreamException {
		String self = null;
		
		Token  d = null;
		
		d = LT(1);
		match(REST_OF_LINE);
		self = d.getText();
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
		"AFFIRM",
		"JAVADOC_CLOSE",
		"EMBEDDED_JML_START",
		"REST_OF_LINE"
	};
	
	
	}
