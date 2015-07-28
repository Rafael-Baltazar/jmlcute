/*
 * Copyright (C) 2008-2009 Federal University of Pernambuco and 
 * University of Central Florida
 *
 * This file is part of AJML
 *
 * AJML is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * AJML is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with AJML; see the file COPYING.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: JmlRacGenerator.java,v 1.0 2008/2/10 17:08:28 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: JmlRacGenerator.java,v 1.21 2006/12/11 20:12:51 chalin Exp $
 * by Yoonsik Cheon
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlAssignmentStatement;
import org.jmlspecs.checker.JmlClassDeclaration;
import org.jmlspecs.checker.JmlClassOrGFImport;
import org.jmlspecs.checker.JmlCompilationUnit;
import org.jmlspecs.checker.JmlInterfaceDeclaration;
import org.jmlspecs.checker.JmlPackageImport;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.checker.JmlVisitor;
import org.multijava.mjc.JClassOrGFImportType;
import org.multijava.mjc.JPackageImportType;
import org.multijava.mjc.JPackageName;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.util.MessageDescription;
import org.multijava.util.compiler.CWarning;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

/**
 * A class implementing the JML Runtime Assertion Checker with AspectJ 
 * features (ARAC). The JML RAC visits and modifies JML ASTs to add runtime 
 * assertion checking code. This class is mainly used for testing various
 * RAC modules being developed.
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public class JmlRacGenerator extends RacAbstractVisitor implements JmlVisitor {

	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Construct a JML RAC generator object
	 */
	public JmlRacGenerator(RacOptions opt, /*@ non_null @*/ Main compiler) {
		newPackageOption = opt.packageName();
		JmlRacGenerator.compiler = compiler;
	}

	// ----------------------------------------------------------------------
	// TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translate a JML compilation unit
	 *
	 * @param self target to translate
	 */
	public void visitJmlCompilationUnit( JmlCompilationUnit self ) 
	{
		isRacable = self.hasSourceInRefinement();
		if (newPackageOption != null) {
			if (newPackageOption.equals("")) {
				newPackageName = "";
			} else if (newPackageOption.endsWith("+")) {
				String n = newPackageOption;
				n = n.substring(0,n.length()-1).replace('.','/');
				n = n + self.packageNameAsString();
				newPackageName = n.substring(0,n.length()-1);
			} else {
				newPackageName = newPackageOption.replace('.','/');
			}
			self.setPackage(new JPackageName(org.multijava.util.compiler.TokenReference.NO_REF,newPackageName,null));  
		}
		// translate types declared in this compilation unit
		JTypeDeclarationType[] typeDecls = self.combinedTypeDeclarations();
		boolean ok = true;
		for (int i = 0; i < typeDecls.length ; i++) {
			JmlTypeDeclaration tdecl = (JmlTypeDeclaration) typeDecls[i];
			tdecl.setHasSourceInRefinement(isRacable);
			if (!Main.isSpecMode(tdecl)) {
				// make sure all concrete methods have bodies
				ok = ok && tdecl.checkRacability(compiler);
			}
		}
		if (!ok) {
			return;
		}
		for (int i = 0; i < typeDecls.length ; i++) {
			typeDecls[i].accept(this);
		}
		// translate model import statements
		JPackageImportType[] pkgs = self.importedPackages();
		for (int i = 0; i < pkgs.length; i++) {
			pkgs[i].accept(this);
		}
		JClassOrGFImportType[] classes = self.importedClasses();
		for (int i = 0; i < classes.length; i++) {
			classes[i].accept(this);
		}
		// add an import statement for RAC runtime classes
		JPackageImportType[] newPkgs = new JPackageImportType[pkgs.length + 1];
		System.arraycopy(pkgs, 0, newPkgs, 0, pkgs.length);
		newPkgs[pkgs.length] = new JmlPackageImport(
				org.multijava.util.compiler.TokenReference.NO_REF,
				"org.jmlspecs.ajmlrac.runtime", null, false);
		self.setImportedPackages(newPkgs);
	}

	/**
	 * Translate a JML import statement into a Java import statement.
	 *
	 * @param self target to translate
	 */
	public void visitJmlPackageImport(JmlPackageImport self) {
		self.unsetModel();
	}

	/**
	 * Translate a JML import statement into a Java import statement.
	 *
	 * @param self target to translate
	 */
	public void visitJmlClassOrGFImport(JmlClassOrGFImport self) {
		self.unsetModel();
	}

	/**
	 * Translate a JML class declaration.
	 *
	 * @param self target to translate
	 */
	public void visitJmlClassDeclaration(JmlClassDeclaration self) 
	{
		TransClass trans = new TransClass(self);
		trans.translate();
	}

	/**
	 * Translate a JML interface declaration.
	 *
	 * @param self target to translate
	 */
	public void visitJmlInterfaceDeclaration(JmlInterfaceDeclaration self) 
	{
		TransInterface trans = new TransInterface(self);
		trans.translate();
	}

	public void visitJmlAssignmentStatement( JmlAssignmentStatement self ) {
		self.assignmentStatement().accept(this);
	}

	/**
	 * Produce a warning message with the given token reference,
	 * message description, and argument to message description. 
	 */
	public static void warn(TokenReference tref, 
			MessageDescription description,
			Object obj) {
		compiler.reportTrouble(new CWarning(tref, description, obj));
	}

	/**
	 * Produce a warning message with the given token reference and
	 * message description.
	 */
	public static void warn(TokenReference tref, 
			MessageDescription description) {
		compiler.reportTrouble(new CWarning(tref, description));
	}


	/**
	 * Produce an error message with the given token reference,
	 * message description, and arguments to message description. 
	 */
	public static void fail(TokenReference tref, 
			MessageDescription description,
			Object obj) {
		compiler.reportTrouble(new PositionedError(tref, description, obj));
	}
	
	public static void fail(TokenReference tref, 
			MessageDescription description,
			Object[] obj) {
		compiler.reportTrouble(new PositionedError(tref, description, obj));
	}

	/**
	 * Produce an error message with the given token reference,
	 * message description, and arguments to message description. 
	 */
	public static void fail(TokenReference tref, 
			MessageDescription description,
			Object obj1,
			Object obj2) {
		compiler.reportTrouble(new PositionedError(tref, description, 
				obj1, obj2));
	}

	// ----------------------------------------------------------------------
	// PROTECTED METHODS
	// ----------------------------------------------------------------------

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** True if the given JML compilation unit is RAC-compilable. */
	private boolean isRacable;

	/** Determines the name of the package or the generated class:
	if null, the package name is the same as the source file package;
	if empty, the package is unnamed;
	if ends with a '+', the string is prepended to the source file package;
	otherwise is the name of the package of the generated class.
	 */
	static public String newPackageOption = null;
	static public String newPackageName = null;

	/** The current compiler to be used for reporting warning messages. */
	private static Main compiler;

	/**
	 * checking_mode tells us what kind of checking is to be done
	 */
	public static final int DEFAULT = 0; //the original JML checking mode
	public static final int WRAPPER = 1; //the wrapper JML checking mode
	public static int checking_mode = DEFAULT;
}
