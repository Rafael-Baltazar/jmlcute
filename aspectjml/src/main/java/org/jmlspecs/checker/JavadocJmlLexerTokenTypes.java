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
		

public interface JavadocJmlLexerTokenTypes {
	int EOF = 1;
	int NULL_TREE_LOOKAHEAD = 3;
	int LITERAL_abstract = 4;
	int LITERAL_assert = 5;
	int LITERAL_boolean = 6;
	int LITERAL_break = 7;
	int LITERAL_byte = 8;
	int LITERAL_case = 9;
	int LITERAL_catch = 10;
	int LITERAL_char = 11;
	int LITERAL_class = 12;
	int LITERAL_const = 13;
	int LITERAL_continue = 14;
	int LITERAL_default = 15;
	int LITERAL_do = 16;
	int LITERAL_double = 17;
	int LITERAL_else = 18;
	int LITERAL_extends = 19;
	int LITERAL_false = 20;
	int LITERAL_final = 21;
	int LITERAL_finally = 22;
	int LITERAL_float = 23;
	int LITERAL_for = 24;
	int LITERAL_goto = 25;
	int LITERAL_if = 26;
	int LITERAL_implements = 27;
	int LITERAL_import = 28;
	int LITERAL_instanceof = 29;
	int LITERAL_int = 30;
	int LITERAL_interface = 31;
	int LITERAL_long = 32;
	int LITERAL_native = 33;
	int LITERAL_new = 34;
	int LITERAL_null = 35;
	int LITERAL_package = 36;
	int LITERAL_private = 37;
	int LITERAL_protected = 38;
	int LITERAL_public = 39;
	int LITERAL_peer = 40;
	int LITERAL_readonly = 41;
	int LITERAL_rep = 42;
	int LITERAL_pure = 43;
	int LITERAL_resend = 44;
	int LITERAL_return = 45;
	int LITERAL_short = 46;
	int LITERAL_static = 47;
	int LITERAL_strictfp = 48;
	int LITERAL_super = 49;
	int LITERAL_switch = 50;
	int LITERAL_synchronized = 51;
	int LITERAL_this = 52;
	int LITERAL_throw = 53;
	int LITERAL_throws = 54;
	int LITERAL_transient = 55;
	int LITERAL_true = 56;
	int LITERAL_try = 57;
	int LITERAL_void = 58;
	int LITERAL_volatile = 59;
	int LITERAL_while = 60;
	int LITERAL__warn = 61;
	int LITERAL__warn_op = 62;
	int LITERAL__nowarn = 63;
	int LITERAL__nowarn_op = 64;
	int ASSIGN = 65;
	int AT = 66;
	int BAND = 67;
	int BAND_ASSIGN = 68;
	int BNOT = 69;
	int BOR = 70;
	int BOR_ASSIGN = 71;
	int BSR = 72;
	int BSR_ASSIGN = 73;
	int BXOR = 74;
	int BXOR_ASSIGN = 75;
	int COLON = 76;
	int COMMA = 77;
	int DEC = 78;
	int DOT = 79;
	int EQUAL = 80;
	int GE = 81;
	int GT = 82;
	int INC = 83;
	int LAND = 84;
	int LBRACK = 85;
	int LCURLY = 86;
	int LE = 87;
	int LNOT = 88;
	int LOR = 89;
	int LPAREN = 90;
	int LT = 91;
	int MINUS = 92;
	int MINUS_ASSIGN = 93;
	int NOT_EQUAL = 94;
	int PERCENT = 95;
	int PERCENT_ASSIGN = 96;
	int PLUS = 97;
	int PLUS_ASSIGN = 98;
	int QUESTION = 99;
	int RBRACK = 100;
	int RCURLY = 101;
	int RPAREN = 102;
	int SEMI = 103;
	int SL = 104;
	int SLASH = 105;
	int SLASH_ASSIGN = 106;
	int SL_ASSIGN = 107;
	int SR = 108;
	int SR_ASSIGN = 109;
	int STAR = 110;
	int STAR_ASSIGN = 111;
	int CHARACTER_LITERAL = 112;
	int IDENT = 113;
	int INTEGER_LITERAL = 114;
	int REAL_LITERAL = 115;
	int STRING_LITERAL = 116;
	int JAVADOC_OPEN = 117;
	int DOT_DOT = 118;
	int LITERAL_BS_TYPE = 119;
	int LITERAL_BS_bigint = 120;
	int LITERAL_BS_bigint_math = 121;
	int LITERAL_BS_duration = 122;
	int LITERAL_BS_elemtype = 123;
	int LITERAL_BS_everything = 124;
	int LITERAL_BS_exists = 125;
	int LITERAL_BS_forall = 126;
	int LITERAL_BS_fresh = 127;
	int LITERAL_BS_into = 128;
	int LITERAL_BS_invariant_for = 129;
	int LITERAL_BS_is_initialized = 130;
	int LITERAL_BS_java_math = 131;
	int LITERAL_BS_lblneg = 132;
	int LITERAL_BS_lblpos = 133;
	int LITERAL_BS_lockset = 134;
	int LITERAL_BS_max = 135;
	int LITERAL_BS_min = 136;
	int LITERAL_BS_nonnullelements = 137;
	int LITERAL_BS_not_modified = 138;
	int LITERAL_BS_not_assigned = 139;
	int LITERAL_BS_not_specified = 140;
	int LITERAL_BS_nothing = 141;
	int LITERAL_BS_nowarn = 142;
	int LITERAL_BS_nowarn_op = 143;
	int LITERAL_BS_num_of = 144;
	int LITERAL_BS_old = 145;
	int LITERAL_BS_only_assigned = 146;
	int LITERAL_BS_only_accessed = 147;
	int LITERAL_BS_only_called = 148;
	int LITERAL_BS_only_captured = 149;
	int LITERAL_BS_other = 150;
	int LITERAL_BS_pre = 151;
	int LITERAL_BS_product = 152;
	int LITERAL_BS_reach = 153;
	int LITERAL_BS_real = 154;
	int LITERAL_BS_result = 155;
	int LITERAL_BS_safe_math = 156;
	int LITERAL_BS_same = 157;
	int LITERAL_BS_space = 158;
	int LITERAL_BS_such_that = 159;
	int LITERAL_BS_sum = 160;
	int LITERAL_BS_type = 161;
	int LITERAL_BS_typeof = 162;
	int LITERAL_BS_warn = 163;
	int LITERAL_BS_warn_op = 164;
	int LITERAL_BS_working_space = 165;
	int LITERAL_U_peer = 166;
	int LITERAL_U_rep = 167;
	int LITERAL_U_readonly = 168;
	int LITERAL_abrupt_behavior = 169;
	int LITERAL_abrupt_behaviour = 170;
	int LITERAL_accessible = 171;
	int LITERAL_accessible_redundantly = 172;
	int LITERAL_also = 173;
	int LITERAL_assert_redundantly = 174;
	int LITERAL_assignable = 175;
	int LITERAL_assignable_redundantly = 176;
	int LITERAL_assume = 177;
	int LITERAL_assume_redundantly = 178;
	int LITERAL_axiom = 179;
	int LITERAL_behavior = 180;
	int LITERAL_behaviour = 181;
	int LITERAL_breaks = 182;
	int LITERAL_breaks_redundantly = 183;
	int LITERAL_callable = 184;
	int LITERAL_callable_redundantly = 185;
	int LITERAL_captures = 186;
	int LITERAL_captures_redundantly = 187;
	int LITERAL_choose = 188;
	int LITERAL_choose_if = 189;
	int LITERAL_code = 190;
	int LITERAL_code_bigint_math = 191;
	int LITERAL_code_contract = 192;
	int LITERAL_code_java_math = 193;
	int LITERAL_code_safe_math = 194;
	int LITERAL_constraint = 195;
	int LITERAL_constraint_redundantly = 196;
	int LITERAL_constructor = 197;
	int LITERAL_continues = 198;
	int LITERAL_continues_redundantly = 199;
	int LITERAL_debug = 200;
	int LITERAL_decreases = 201;
	int LITERAL_decreases_redundantly = 202;
	int LITERAL_decreasing = 203;
	int LITERAL_decreasing_redundantly = 204;
	int LITERAL_diverges = 205;
	int LITERAL_diverges_redundantly = 206;
	int LITERAL_duration = 207;
	int LITERAL_duration_redundantly = 208;
	int LITERAL_ensures = 209;
	int LITERAL_ensures_redundantly = 210;
	int LITERAL_example = 211;
	int LITERAL_exceptional_behavior = 212;
	int LITERAL_exceptional_behaviour = 213;
	int LITERAL_exceptional_example = 214;
	int LITERAL_exsures = 215;
	int LITERAL_exsures_redundantly = 216;
	int LITERAL_extract = 217;
	int LITERAL_field = 218;
	int LITERAL_forall = 219;
	int LITERAL_for_example = 220;
	int LITERAL_ghost = 221;
	int LITERAL_helper = 222;
	int LITERAL_hence_by = 223;
	int LITERAL_hence_by_redundantly = 224;
	int LITERAL_implies_that = 225;
	int LITERAL_in = 226;
	int LITERAL_in_redundantly = 227;
	int LITERAL_initializer = 228;
	int LITERAL_initially = 229;
	int LITERAL_instance = 230;
	int LITERAL_invariant = 231;
	int LITERAL_invariant_redundantly = 232;
	int LITERAL_loop_invariant = 233;
	int LITERAL_loop_invariant_redundantly = 234;
	int LITERAL_maintaining = 235;
	int LITERAL_maintaining_redundantly = 236;
	int LITERAL_maps = 237;
	int LITERAL_maps_redundantly = 238;
	int LITERAL_measured_by = 239;
	int LITERAL_measured_by_redundantly = 240;
	int LITERAL_method = 241;
	int LITERAL_model = 242;
	int LITERAL_model_program = 243;
	int LITERAL_modifiable = 244;
	int LITERAL_modifiable_redundantly = 245;
	int LITERAL_modifies = 246;
	int LITERAL_modifies_redundantly = 247;
	int LITERAL_monitored = 248;
	int LITERAL_monitors_for = 249;
	int LITERAL_non_null = 250;
	int LITERAL_non_null_by_default = 251;
	int LITERAL_normal_behavior = 252;
	int LITERAL_normal_behaviour = 253;
	int LITERAL_normal_example = 254;
	int LITERAL_nullable = 255;
	int LITERAL_nullable_by_default = 256;
	int LITERAL_old = 257;
	int LITERAL_or = 258;
	int LITERAL_post = 259;
	int LITERAL_post_redundantly = 260;
	int LITERAL_pre = 261;
	int LITERAL_pre_redundantly = 262;
	int LITERAL_query = 263;
	int LITERAL_readable = 264;
	int LITERAL_refine = 265;
	int LITERAL_refines = 266;
	int LITERAL_refining = 267;
	int LITERAL_represents = 268;
	int LITERAL_represents_redundantly = 269;
	int LITERAL_requires = 270;
	int LITERAL_requires_redundantly = 271;
	int LITERAL_returns = 272;
	int LITERAL_returns_redundantly = 273;
	int LITERAL_secret = 274;
	int LITERAL_set = 275;
	int LITERAL_signals = 276;
	int LITERAL_signals_only = 277;
	int LITERAL_signals_only_redundantly = 278;
	int LITERAL_signals_redundantly = 279;
	int LITERAL_spec_bigint_math = 280;
	int LITERAL_spec_java_math = 281;
	int LITERAL_spec_protected = 282;
	int LITERAL_spec_public = 283;
	int LITERAL_spec_safe_math = 284;
	int LITERAL_static_initializer = 285;
	int LITERAL_uninitialized = 286;
	int LITERAL_unreachable = 287;
	int LITERAL_weakly = 288;
	int LITERAL_when = 289;
	int LITERAL_when_redundantly = 290;
	int LITERAL_working_space = 291;
	int LITERAL_working_space_redundantly = 292;
	int LITERAL_writable = 293;
	int INFORMAL_DESC = 294;
	int IMPLIES = 295;
	int BACKWARD_IMPLIES = 296;
	int EQUIV = 297;
	int NOT_EQUIV = 298;
	int R_ARROW = 299;
	int L_ARROW = 300;
	int SUBTYPE_OF = 301;
	int LCURLY_VBAR = 302;
	int VBAR_RCURLY = 303;
	int AFFIRM = 304;
	int JAVADOC_CLOSE = 305;
	int EMBEDDED_JML_START = 306;
	int REST_OF_LINE = 307;
	int DOC_NL_WS = 308;
	int NEWLINE = 309;
	int NON_NL_WS_OPT = 310;
}
