/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of the JML project.  More information is 
 * available from www.jmlspecs.org.
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
 * $Id: TokenStreamSelector.java,v 1.9 2005/01/08 19:03:54 cheon Exp $
 */

package org.jmlspecs.checker;

import java.util.LinkedList;

import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.MjcTokenTypes;
import org.multijava.util.compiler.CToken;
import org.multijava.util.compiler.PositionedError;

import antlr.Token;

/**
 * Provides for switching between various lexical analyzers for lexing
 * JML.  Extends antlr.TokenStreamSelector by providing some shared
 * state for the lexical analyzers.  This shared state tracks whether
 * the IDENTs being lexed appear in a regular Java context, a regular
 * JML annotation context, or within a JML expression.  The same IDENT
 * is matched against a different set of keywords in the different
 * contexts.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.9 $
 */
public class TokenStreamSelector extends antlr.TokenStreamSelector {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public TokenStreamSelector() {
	super();
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public final void lexedLeftParen() {
	parenCount++;
    }

    public final void lexedRightParen() {
	parenCount--;
    }

    public final void lexedSemicolon() {
	if (parenCount == 0) {
	    inJMLExpression = false;
            inJMLModelMethodConstructorHeader = false;
	}
    }

    public final void lexedLCurly() {
	if (inJMLModelTypeHeader) {
	    inJMLModelTypeHeader = false;
	    inJMLExpression = false;
	    rstack.addFirst(MODELTYPE);
	} else if (inJMLModelMethodConstructorHeader) {
            inJMLModelMethodConstructorHeader = false;
            inJMLExpression = false;
	    rstack.addFirst(MODELCONSTRUCTOR);
        } else if (inJMLExpression) {
	    intstack.addFirst(new Integer(parenCount));
	    parenCount = 0;
	    inJMLExpression = false;
	    rstack.addFirst(INEXPRESSION);
        } else {
	    intstack.addFirst(new Integer(parenCount));
	    parenCount = 0;
	    inJMLExpression = false;
	    rstack.addFirst(NOTINEXPRESSION);
        }
    }

    public final void lexedRCurly(Token tok) {
	Object o = rstack.removeFirst();
	if (o == INEXPRESSION || o == NOTINEXPRESSION) {
	    if (parenCount != 0) {
		/* I think the grammar prevents us from ever getting
		   here, but just in case...
                */
		CTopLevel.getCompiler().reportTrouble(
		  new PositionedError(
		    ((CToken)tok).makeTokenReference(),
		    JmlMessages.UNBALANCED_PAREN));
	    }
	    parenCount = ((Integer)intstack.removeFirst()).intValue();
	    inJMLExpression = o == INEXPRESSION;
        }
    }

    /**
     * Returns the appropriate token for the JML ident contained in
     * <CODE>charCache[start]..charCache[start+length]</CODE>, or
     * <CODE>null</CODE> if no JML ident is appropriate.  The token
     * table searched depends on whether or the lexical analyzers are
     * processing a JML expression or just a regular annotation.  The
     * result of this method is only valid if the lexical analysis is
     * actually processing an annotation.
     *
     * Note the various logic in this class for keeping track of whether
     * inJMLExpression should be true or false.  We have to do this based
     * on the token stream - hence the calls alerting to the processing of
     * various punctuation marks.  If we try invoking some information from
     * the parser, we will get in trouble, because the lexer is a few tokens
     * ahead of the parser, because of lookahead (and the amount will vary
     * depending on what lookahead various rules of the grammar need).
     *
     * The essential piece of logic is that a semicolon terminates a JML
     * expression, as long as it is not inside braces or parentheses (as in
     * quantifier expressions).  Note that within an expression one can have
     * method calls on anonymous classes that contain method definitions -
     * full-fledged code.  So maintaining inJMLExpression is tricky.
     * You are welcome to improve on what is here (but test it well!)
     *                         - DRCok 7/25/2003
     * <pre><jml>
     * requires (* token in charCache appears inside a JML annotation *);
     * </jml></pre>
     *
     */
    public final CToken lookupJMLToken( char[] charCache, int start, int tokenLen ) {
	CToken tok = lookupKeyword( charCache, 0, tokenLen );
	if (tok != null) {
            int tokType = tok.getType();

            // WMD special treatment of some tokens
	    if( inJMLExpression &&
	        !allowUniverseKeywords &&
		(tokType == MjcTokenTypes.LITERAL_peer ||
		 tokType == MjcTokenTypes.LITERAL_readonly ||
		 tokType == MjcTokenTypes.LITERAL_rep ||
		 tokType == MjcTokenTypes.LITERAL_pure ) ) {
		// WMD pretend nothing happened :-)
		return null;
	    }

	    if (tokType == JmlTokenTypes.LITERAL_assert) {
		// We can't just do a setType on tok, because tok has
		// a static alias in JmlIDKeywords!  So we use a
		// static token here.
		tok = HACKED_AFFIRM_LITERAL_TOKEN;
	    }

	    if (tok.hasFlag(JmlIDKeywords.IGNORE_JML_ID_AFTER)
                // switch out of JML mode after reading import in
                // a "model import" directive.
                || tokType == MjcTokenTypes.LITERAL_import) {
		inJMLExpression = true;
                if (tokType == JmlTokenTypes.LITERAL_method
                    || tokType == JmlTokenTypes.LITERAL_constructor) {
                    inJMLModelMethodConstructorHeader = true;
                }
	    }

            if (tokType == MjcTokenTypes.LITERAL_class
                || tokType == MjcTokenTypes.LITERAL_interface) {
                inJMLExpression = true;
                inJMLModelTypeHeader = true;
            }

	}
	return tok;
    }

    /** Looks up keywords. If the current token is not a keyword, null
     * is returned. */
    protected CToken lookupKeyword( char[] charCache, int start, 
                                    int tokenLen ) {
	if (inJMLExpression) {
	    return JmlExprIDKeywords.lookup( charCache, 0, tokenLen );
	} else {
	    return JmlIDKeywords.lookup( charCache, 0, tokenLen );
	}
    }

    /** WMD
     */
    public void setAllowUniverseKeywords( boolean flag ) {
	allowUniverseKeywords = flag;
    }


    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /**
     * Flag indicates whether we are lexing within a JML expression.  Used
     * to switch between keyword tables for resolving IDENTs.
     */
    protected boolean inJMLExpression = false;

    /**
     * Flag indicates whether we are lexing within the header of a
     * model class or interface declaration.  Used to switch between
     * keyword tables for resolving IDENTs.
     */
    private boolean inJMLModelTypeHeader = false;
    
    /**
     * Flag indicates whether we are lexing within the header of a
     * model method or constructor declaration.  Used to switch between
     * keyword tables for resolving IDENTs.
     */
    private boolean inJMLModelMethodConstructorHeader = false;

    /**
     * Flag indicates whether we are lexing within a JML quantifier
     * expression.  Used to detect whether or not a ';' indicates the
     * end of a JML expression.
     */
    private boolean inQuantifier = true; //false;
    
    /**
     * Count of the number of left parens without matching right
     * parens found within a JML expression.  Used to detect whether
     * or not a ';' indicates the end of a JML expression.
     */
    private int parenCount = 0;

    // WMD
    private boolean allowUniverseKeywords = false;

    /**
     * This token is returned whenever an assert token is lexed inside
     * a JML annotation.
     */
    private CToken HACKED_AFFIRM_LITERAL_TOKEN = 
	new CToken( JmlIDTokenTypes.AFFIRM, "assert", 
		    JmlIDKeywords.IGNORE_JML_ID_AFTER );

    /** This stack keeps track of parenthesis nesting level as we move into
	inner {} contexts.
    */
    private LinkedList intstack = new LinkedList();

    /** This stack keeps track of the different kinds of {} contexts we are
	in within what is at the top level a JML expression.
    */
    private LinkedList rstack = new LinkedList();
    // elements of rstack are each one of these
    /*@ private invariant
	(\forall Object o; rstack.contains(o); o == NOTINEXPRESSION ||
	    o == MODELTYPE || o == MODELCONSTRUCTOR || o == INEXPRESSION );
    */
	static private final Object MODELTYPE = new Object();
	static private final Object MODELCONSTRUCTOR = new Object();
	static private final Object INEXPRESSION = new Object();
	static private final Object NOTINEXPRESSION = new Object();
}
