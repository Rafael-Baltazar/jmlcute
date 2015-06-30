/** @(#)$Id: RacRunTestCase.java,v 1.3 2006/12/19 18:19:03 chalin Exp $
 *
 * By subclassing <code>RacRunTestCase</code>, you can write a normal
 * JUnit test file and yet use it as a test case for the racrun
 * package (which expects test failure to be reported in a very
 * specific format and not output otherwise).
 *
 * Usage:
 * <pre>
 * public class MyTestCase extends org.jmlspecs.util.RacRunTestCase {
 * 
 *     MyTestCase testee = new MyTestCase();
 * 
 *     public static void main(String[] args) {
 * 	(new MyTestCase()).run(args);
 *     }
 * 
 *     // Rest of the file is like a normal JUnit TestCase
 * 
 *     public void test_one(int i) {
 * 	assertEquals(1, i);
 *     }
 *     ...
 * }
 * </pre>
 * To run this test case and see the usual JUnit text runner output
 * use the -v option: <code>java MyTestCase -v</code>.
 *
 * @author Patrice Chalin (chalin@dsrg.org)
 * @version $Revision: 1.3 $
 */

package org.jmlspecs.util;

import java.io.*;
import org.jmlspecs.ajmlrac.runtime.*;

public class RacRunTestCase extends junit.framework.TestCase {

    private static int fcnt;

    public void run(String[] args) {
	String outputFileName = "junit-test-output.txt";
	if(args.length > 0) {
	    if(args.length == 1 && "-v".equals(args[0])) {
		outputFileName = "";
	    } else {
		System.err.println("Unexpected arguments\nUsage <testcase> [-v].");
		return;
	    }
	}
	run(outputFileName);
    }

    public void run(String outputFileName) {
	fcnt = 0;

	// The JUnit test runner produces output by default (e.g. a
	// "." for each test and the total test time).  This can
	// interfere with the diagnostics of the racrun test, hence in
	// some cases we write the JUnit output to a file.
	boolean quiet = outputFileName == null || "".equals(outputFileName);
	if(quiet) {
	    // Let the default junit text runner output be sent to
	    // System.out (this include the "." and the time).
	    junit.textui.TestRunner.run(this.getClass());
	} else {
	    // Write the test
	    runButWriteToFile(outputFileName);
	}
	if (fcnt > 0)
	    System.out.println(fcnt + "F(" + this.getClass().getName() + ".java)");
    }

    private void runButWriteToFile(String outputFileName) {
	FileOutputStream f = null;
	try {
	    f = new FileOutputStream(outputFileName);
	} catch (java.io.FileNotFoundException e) {
	    System.err.println(e.toString());
	    return;
	}
	PrintStream s = new PrintStream(f);
	s.println(this.getClass().getName());
	junit.textui.TestRunner t =  new junit.textui.TestRunner(s);
	t.doRun(new junit.framework.TestSuite(this.getClass()));
    }

    public static void fail() {
	fcnt++;
	junit.framework.TestCase.fail();
    }	

    public static void fail(String s) {
	fcnt++;
	junit.framework.TestCase.fail(s);
    }	

    public void checkJmlErr(Class c, JMLAssertionError e) {
	if(org.jmlspecs.ajmlrac.runtime.JMLRacUtil.oldSem()) {
	    junit.framework.Assert.
		assertTrue("expected:<" + c + "> but was:<" + e + ">",
			   c.isAssignableFrom(e.getClass()));
	} else {
	    junit.framework.Assert.
		assertTrue("expected:<JMLEvaluationError" +
			   "> but was:<" + e + ">",
			   e instanceof JMLEvaluationError);
	    junit.framework.Assert.
		assertTrue("expected:<" + c + 
			   "> but was:<" + e.getCause() + ">",
			   org.jmlspecs.ajmlrac.runtime.JMLRacUtil.matchCause(c,e));
	}
    }
}

// Copyright (C) 2006 Iowa State University
//
// This file is part of JML
//
// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.
//
// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
