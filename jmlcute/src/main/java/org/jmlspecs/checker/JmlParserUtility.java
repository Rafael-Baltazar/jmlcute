package org.jmlspecs.checker;
import org.multijava.javadoc.JavadocComment;
import org.multijava.mjc.ParserUtility;
import org.multijava.mjc.ParsingController;

import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenStream;
import antlr.TokenStreamException;

/** This class is derived from ...mjc.ParserUtility; its purpose is to supply
	a different JavadocParser than the one in org.multijava.mjc.
*/
public class JmlParserUtility extends ParserUtility {

    public JmlParserUtility( org.multijava.mjc.Main compiler, 
			     ParsingController parsingController,
                             boolean allowGeneric,
			     boolean allowMultiJava, 
			     boolean allowRelaxedMultiJava, 
			     boolean allowUniverseKeywords, // WMD
			     boolean parseJavadocs ) 
    {
	super( compiler, parsingController, allowGeneric,
	       allowMultiJava, allowRelaxedMultiJava, 
	       allowUniverseKeywords, // WMD
	       parseJavadocs );
    }

    /**
     * Supplies an AST for the javadoc style comment preceding the
     * given token. */
    public JavadocComment getJavadocComment( Token tok ) 
	throws TokenStreamException, RecognitionException
    {
	if( !parseJavadocs ) {
	    return null;
	}
	try {
	    TokenStream tokStream = parsingController.streamForBefore( "javadoc", tok );
	    JavadocJmlParser parser = new JavadocJmlParser( tokStream ); 
			
	    return parser.docComment();
	} catch( ParsingController.KeyException ke ) {
	    throw 
		new RecognitionException( "unable to establish javadoc parser." );
	}
    }

}
