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
 * $Id: InvariantMethodAdviceAsPostconditionMethod.java,v 1.0 2009/01/21 22:03:15 henriquerebelo Exp $
 */

package org.jmlspecs.ajmlrac;

import org.jmlspecs.checker.JmlClassDeclaration;
import org.jmlspecs.checker.JmlTypeDeclaration;
import org.jmlspecs.util.AspectUtil;

/**
 * A class for generating assertion check methods for class-level
 * assertions such as invariants and history constraints.
 * There are two types of class-level assertions:
 * <em>instance</em> (<em>non-static</em>) <em>assertions</em> and
 * <em>class</em> (<em>static</em>) <em>assertions</em>.
 * As thus, two types of assertion check methods are generated. 
 * An instance assertion check method checks both the instance and class 
 * assertions while a class assertion check method checks only the class 
 * assertionss. 
 * The generated assertion check methods inherit assertions of its superclass
 * interfaces by dynamically invoking the corresponding assertion methods.
 *
 * <p>
 * The class implements a variant of the <em>Template Pattern</em>
 * [GoF95], prescribed in the class {@link AssertionMethod}.
 * </p>
 *
 * @see AssertionMethod
 *
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public abstract class InvariantLikeMethod extends AssertionMethod{
	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/** Construct a new <code>InvariantLikeMethod</code> object. 
	 *
	 * @param isStatic the kind of assertion check method to generate;
	 *                 <tt>true</tt> for static and <tt>false</tt> for 
	 *                 non-static (instance) assertion check method.
	 * @param typeDecl the target type declaration whose assertion check
	 *                 methods are to be generated.
	 */
	public InvariantLikeMethod(boolean isStatic, JmlTypeDeclaration typeDecl, VarGenerator varGen)
	{ 
		this.isStatic = isStatic;
		this.typeDecl = typeDecl;
		this.varGen = varGen;
		this.exceptionToThrow = "JMLInvariantError";
		this.checkInvariantVisibilityRules(varGen);
		this.instInvPred = AspectUtil.changeThisOrSuperRefToAdviceRef(this.combineInvariantsWithNonNull(INST_INV, varGen), typeDecl);
		this.statInvPred = this.combineInvariantsWithNonNull(STAT_INV, varGen);
		
		this.hasInstInv = !instInvPred.equals("");
		this.hasStatInv = !statInvPred.equals("");
		
		this.statInvPred = AspectUtil.replaceDollaSymbol(this.statInvPred);

		//		javadoc to be added to the generated invariant method	
		if( (this.hasInstInv) && (this.hasStatInv)){	
			this.javadoc = "/** Generated by AspectJML to check " + 
			"non-static" + " invariants of \n" + 
			((this.typeDecl instanceof JmlClassDeclaration) ? 
					" * class " : " * interface ") +
					this.typeDecl.ident() + ". */";
			this.javadocStat = "/** Generated by AspectJML to check " + 
			"static" + " invariants of \n" + 
			((this.typeDecl instanceof JmlClassDeclaration) ? 
					" * class " : " * interface ") +
					this.typeDecl.ident() + ". */";
		}
		else if (this.hasInstInv){
			this.javadoc = "/** Generated by AspectJML to check " + 
			"non-static" + " invariants of \n" + 
			((this.typeDecl instanceof JmlClassDeclaration) ? 
					" * class " : " * interface ") +
					this.typeDecl.ident() + ". */";
		}
		else if (this.hasStatInv){
			this.javadoc = "/** Generated by AspectJML to check " + 
			"static" + " invariants of \n" + 
			((this.typeDecl instanceof JmlClassDeclaration) ? 
					" * class " : " * interface ") +
					this.typeDecl.ident() + ". */";
		}
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------	
	protected final /*@ spec_public non_null @*/ VarGenerator varGen;
	
	protected static boolean INST_INV = false;
	protected static boolean STAT_INV = true;

	protected boolean hasInstInv = false;
	protected boolean hasStatInv = false;
	protected /*@ nullable */ String javadocStat;
	protected String instInvPred = "";
	protected String statInvPred = "";

}