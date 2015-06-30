/*
 * Copyright (C) 2003 Iowa State University
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
 * $Id: Constants.java,v 1.2 2004/07/10 03:36:03 kui_dai Exp $
 */

package org.jmlspecs.util.dis;

/**
 * Defines disassembler constants
 */
public interface Constants {

    int ACC_MODEL		= 0x00010000;
    int ACC_PURE		= 0x00020000;
    int ACC_INSTANCE		= 0x00040000;
    int ACC_SPEC_PUBLIC		= 0x00080000;
    int ACC_SPEC_PROTECTED	= 0x00100000;
    int ACC_GHOST		= 0x00200000;
    int ACC_MONITORED		= 0x00400000;
    int ACC_UNINITIALIZED	= 0x00800000;
    int ACC_NON_NULL		= 0x01000000;
    int ACC_HELPER		= 0x02000000;

    int ACC_CODE_JAVA_MATH	= 0x04000000;
    int ACC_CODE_SAFE_MATH	= 0x08000000;
    int ACC_CODE_BIGINT_MATH	= 0x10000000;
    int ACC_SPEC_JAVA_MATH	= 0x20000000;
    int ACC_SPEC_SAFE_MATH	= 0x40000000;
    int ACC_SPEC_BIGINT_MATH	= 0x80000000;

    int ACC2_RAC_METHOD         = 0x00000001;
}

