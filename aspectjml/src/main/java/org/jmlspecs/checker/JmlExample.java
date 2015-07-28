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
 * $Id: JmlExample.java,v 1.9 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.*;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;

/**
 * A class representing JML example specifications. An example
 * specification is a redundant specification
 * (<code>redundant-spec</code>).  The production rule for example
 * specifications, <code>example</code> is defined as follows.
 * <p/>
 * <pre>
 *  example ::= [ [ privacy ] ] "example" ] [ spec-var-decls ]
 *      [ spec-header ] simple-spec-body
 *    | [ privacy ] "exceptional_example" [ spec-var-decls ]
 *      spec-header [ exceptional-example-body ]
 *    | [ privacy ] "exceptional_example" [ spec-var-decls ]
 *      exceptional-example-body
 *    | [ privacy ] "normal_example" [ spec-var-decls ]
 *      spec-header [ normal-example-body ]
 *    | [ privacy ] "normal_example" [ spec-var-decls ]
 *      normal-example-body
 * </pre>
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.9 $
 */

public class JmlExample extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    /**
     * Constructs a new instance with given arguments. The created
     * instance is an AST for a heavy-weighted example specification.
     * <p/>
     * <pre><jml>
     * requires privacy == 0 ||
     *   privacy == Constants.ACC_PUBLIC ||
     *   privacy == Constants.ACC_PROTECTED ||
     *   privacy == Constants.ACC_PRIVATE;
     * </jml></pre>
     */
    public JmlExample(TokenReference where,
                      long privacy,
                      JmlSpecVarDecl[] specVarDecls,
               /*@ non_null @*/ JmlRequiresClause[] specHeader,
                       /*@ non_null @*/ JmlSpecBodyClause[] specBody) {
        super(where);
        this.lightWeighted = false;
        this.privacy = privacy;
        this.specVarDecls = specVarDecls;
        this.specHeader = specHeader;
        this.specBody = specBody;
    }

    /**
     * Constructs a new instance with given arguments. The created
     * instance is an AST for a light-weighted example specification.
     */
    public JmlExample(TokenReference where,
                      JmlSpecVarDecl[] specVarDecls,
                       /*@ non_null @*/ JmlRequiresClause[] specHeader,
                       /*@ non_null @*/ JmlSpecBodyClause[] specBody) {
        this(where, 0, specVarDecls, specHeader, specBody);
        this.lightWeighted = true;
    }

    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /**
     * Returns true if this example specification is light-weighted.
     * <p/>
     * <pre><jml>
     * ensures \result == lightWeighted;
     * </jml></pre>
     */
    public /*@ pure @*/ boolean isLightWeighted() {
        return lightWeighted;
    }

    public /*@ pure @*/ long privacy() {
        return privacy;
    }

    public /*@ pure @*/ JmlSpecVarDecl[] specVarDecls() {
        return specVarDecls;
    }

    public /*@ pure non_null @*/ JmlRequiresClause[] specHeader() {
        return specHeader;
    }

    /**
     * Deprecated
     */
    public /*@ pure non_null @*/ JmlSpecBodyClause[] specClauses() {
        return specBody;
    }

    public /*@ pure non_null @*/ JmlSpecBodyClause[] specBody() {
        return specBody;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    /**
     * Typechecks the <code>example</code> the context in which it
     * appears. Mutates the context to record the information learned
     * during checking.
     *
     * @param context the context in which this appears
     * @throws PositionedError if any checks fail
     */
    public void typecheck(CFlowControlContextType context)
            throws PositionedError {
        // determine the privacy of this example specification.
        long privacy = lightWeighted ? privacy(context) : this.privacy;
        // create temp context for storing spec vars
        // newCtx -> newBlock -> orgBody (context) -> ...
        CFlowControlContextType newCtx = context;
        if (specVarDecls != null) {
            newCtx = context.createFlowControlContext(getTokenReference());
            for (int i = 0; i < specVarDecls.length; i++) {
                specVarDecls[i].typecheck(newCtx, privacy);
            }
        }
        if (specHeader != null) {
            for (int i = 0; i < specHeader.length; i++) {
                if (specHeader[i] != null) {
                    specHeader[i].typecheck(newCtx, privacy);
                }
            }
        }
        if (specBody != null) {
            for (int i = 0; i < specBody.length; i++) {
                if (specBody[i] != null) {
                    specBody[i].typecheck(newCtx, privacy);
                }
            }
        }
        // clean up temp contexts
        if (specVarDecls != null) {
            newCtx.checkingComplete();
        }
    }

    /**
     * Returns the privacy of this node. By default, it returns that
     * of the method being checked. If the method has either
     * SPEC_PUBLIC or SPEC_PROTECTED modifier, then that modifier
     * takes precedence over the JAVA access modifiers.
     */
    protected long privacy(CFlowControlContextType context) {
        //@ assert context.getCMethod() != null;
        long modifiers = context.getCMethod().modifiers();
        long privacy = modifiers & (ACC_SPEC_PUBLIC | ACC_SPEC_PROTECTED);
        if (privacy == 0) {
            privacy = modifiers & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE);
        }
        return privacy;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     *
     * @param p the visitor
     */
    public void accept(MjcVisitor p) {
        if (p instanceof JmlVisitor)
            ((JmlVisitor) p).visitJmlExample(this);
        else
            throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    /*@ private invariant privacy == 0 ||
      @    privacy == Constants.ACC_PUBLIC ||
      @    privacy == Constants.ACC_PROTECTED ||
      @    privacy == Constants.ACC_PRIVATE;
      @*/
    private long privacy;

    private JmlSpecVarDecl[] specVarDecls;
    private /*@ non_null @*/ JmlRequiresClause[] specHeader;
    private /*@ non_null @*/ JmlSpecBodyClause[] specBody;

    /**
     * Indicates whether this example specification is light-weighted
     * or not.
     */
    /*@ spec_public @*/ private boolean lightWeighted;

} // JmlExample
