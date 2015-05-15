/*
 * Copyright (C) 2001, 2002 Iowa State University
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
 * $Id: TransConstructorBody.java,v 1.7 2004/01/22 19:59:35 leavens Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.*;
import org.multijava.mjc.JTypeDeclarationType;

/**
 * A visitor class for translating JML specification statements in 
 * a constrcutor body into assertion check code. The translated assertion
 * check code is stored as a <code>RacNode</code> in the AST of the 
 * specification statement and is expected to be pretty-printed by
 * the class {@link RacPrettyPrinter}. Translated are such specification
 * statements as <code>assume</code>, <code>assert</code>, and
 * <code>unreachable</code> statements.
 *
 * @see #translate()
 * @see TransMethodBody#visitJmlAssumeStatement(JmlAssumeStatement)
 * @see TransMethodBody#visitJmlAssertStatement(JmlAssertStatement)
 * @see TransMethodBody#visitCompoundStatement(JStatement[])
 * @see TransMethodBody#visitJmlUnreachableStatement(JmlUnreachableStatement)

 * @author Yoonsik Cheon
 * @version $Revision: 1.7 $
 */
public class TransConstructorBody extends TransMethodBody {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Construct an object of <code>TransConstructorBody</code>.
     *
     * @param varGen variable name generator
     * @param mdecl constructor body to be translated
     */
    public TransConstructorBody(/*@ non_null @*/ VarGenerator varGen,
                                /*@ non_null @*/ JmlMethodDeclaration mdecl,
				/*@ non_null @*/ JTypeDeclarationType typeDecl) {
	super(varGen, mdecl, typeDecl);
    }
}

