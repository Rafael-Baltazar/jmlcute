/* $Id: JMLRacBigIntegerUtils.java,v 1.2 2005/07/07 21:03:03 leavens Exp $
 *
// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.
 */

package org.jmlspecs.ajmlrac.runtime;

/**
 * A class for providing some methods to support \bigint in RAC
 *
 * @author Patrice Chalin; Kui Dai
 * @version $Revision: 1.2 $
 */

import java.math.BigInteger;

public class JMLRacBigIntegerUtils {

    // ----------------------------------------------------------------------
    // CONSRUCTORS AND FACTORY METHODS
    // ----------------------------------------------------------------------
    
    /**
     * Constructs a new instance. */
    private JMLRacBigIntegerUtils() {
    }

    // ----------------------------------------------------------------------
    // ACCESSORS
    // ----------------------------------------------------------------------

    /**
     * This method is used in the RAC implementation of prefix ++ and
     * -- over \bigint's. Given \bigint bi, we translate ++bi into
     * value(bi = bi.add(BigInteger.ONE)).  The reason that ++bi is
     * not simply transated into (bi = bi.add(BigInteger.ONE)) is that
     * expressions cannot be used where a statement is expected where
     * as a method call like value(...) can.
     */
    //@ ensures \result == i;
    public /*@pure@*/ static BigInteger value(BigInteger i) { return i; }
    
    /**
     * This method is used in the RAC implementation of postfix ++ and
     * -- over \bigint's. E.g. given \bigint bi, we translate bi++ into
     * first(bi, bi = bi.add(BigInteger.ONE)).
     */
    //@ ensures \result == i;
    public /*@pure@*/ static BigInteger first(BigInteger i, BigInteger j) {
	return i;
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
    
}
