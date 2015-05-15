/*
 * Copyright (C) 2001 Iowa State University
 *
 * This file is part of JML
 *
 * JML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * JML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with JML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: RacContext.java,v 1.4 2003/03/15 20:33:12 davidcok Exp $
 */

package org.jmlspecs.ajmlrac;

/**
 * A class for representing contexts for translating JML expressions.
 * A translation context can be either <em>positive</em> or
 * <em>negative</em>. In a positive context, JML expressions are
 * translated in such a way as to interpret runtime exceptions thrown
 * by the expressions as <code>false</code>. In a negative context,
 * the exceptions are interpreted as <code>true</code>. If a context
 * is disabled, no interpretation is made, i.e., exceptions are
 * further propagated into the enclosing expression.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.4 $
 */

public class RacContext {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /** Construct a new context of the given type. 
     *
     * @param type Type of context to create. It is either
     * <code>CTX_POSITIVE</code> or <code>CTX_POSITIVE</code>. */
    private RacContext(int type) {
        this.type = type;
        this.enabled = true;
    }

    /** Returns a new positive context. */
    public static RacContext createPositive() {
        return new RacContext(CTX_POSITIVE);
    }

    /** Returns a new negative context. */
    public static RacContext createNegative() {
        return new RacContext(CTX_NEGATIVE);
    }

    /** Returns a new neutral context. A neutral contex is a positive
     * context, but disabled. */
    public static RacContext createNeutral() {
        RacContext ctx = new RacContext(CTX_POSITIVE);
        ctx.disable();
        return ctx;
    }

    /** Returns a new context that has the opposite polarity to the
     * given context, but with the same status. */
    public static RacContext createOpposite(RacContext ctx) {
        RacContext newCtx = new RacContext(
            ctx.isPositive() ? CTX_NEGATIVE : CTX_POSITIVE);
        newCtx.setEnabled(ctx.enabled);
        return newCtx;
    }

    // ----------------------------------------------------------------------
    // QUERY METHODS
    // ----------------------------------------------------------------------

    /** Returns true if this context is a positive context. */
    public boolean isPositive() {
        return type == CTX_POSITIVE;
    }

    /** Returns true if this context is a negative context. */
    public boolean isNegative() {
        return type == CTX_NEGATIVE;
    }

    /** Returns the string form of statement expression that sets the
     * variable, <code>var</code>, to the value for an angelic
     * undefinedness. For example, return value is <code>var + " =
     * true"</code> for a positive context and <code>var + " =
     * false</code> for a negative context. It is <code>"throw new
     * JMLNonExecutableException()"</code> if this context is disabled. */
    public String angelicValue(String var) {
        if (!enabled) {
            return "throw JMLChecker.ANGELIC_EXCEPTION";
        }
        return var + (isPositive() ? " = true" : " = false");
    }

    /** Returns the string form of statement expression that sets the
     * variable, <code>var</code>, to the value for an demonic
     * undefinedness. For example, return value is <code>var + " =
     * false"</code> for a positive context and <code>var + " =
     * true</code> for a negative context. It is <code>"throw new
     * RuntimeException()"</code> if this context is disabled. */
    public String demonicValue(String var) {
        if (!enabled) {
            return "throw JMLChecker.DEMONIC_EXCEPTION";
        }
        return var + (isPositive() ? " = false" : " = true");
    }

    /** Returns true if contextual interpretation is enabled. */
    public boolean enabled() {
        return enabled;
    }

    /** Enables contextual interpretation. */
    public void enable() {
        enabled = true;
    }

    /** Disables contextual interpretation. */
    public void disable() {
        enabled = false;
    }

    /** Changes the type of this context. E.g., from positive to
     * negative, or negative to positive. */
    public void changePolarity() {
        type = (isPositive() ? CTX_NEGATIVE : CTX_POSITIVE);
    }

    /** Enables or diables contextual interpretation. */
    public void setEnabled(boolean status) {
        this.enabled = status;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------

    private final static int CTX_POSITIVE = 0;
    private final static int CTX_NEGATIVE = 1;

    /** Type of this context. It is either <code>CTX_POSITIVE</code> or
     * <code>CTX_POSITIVE</code>. */
    private int type; 

    /** Indicates whether this context is enabled or not. */
    private boolean enabled;
}

