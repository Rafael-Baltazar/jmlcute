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
 * $Id: JmlRefinePrefix.java,v 1.24 2004/07/02 07:15:06 leavens Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.io.IOException;

import org.multijava.mjc.CTopLevel;
import org.multijava.mjc.JCompilationUnitType;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.MjcVisitor;
import org.multijava.util.classfile.ClassFileFormatException;
import org.multijava.util.classfile.ClassInfo;
import org.multijava.util.classfile.ClassPath;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;

public class JmlRefinePrefix extends JmlNode {

    //---------------------------------------------------------------------
    // CONSTRUCTORS
    //---------------------------------------------------------------------

    public JmlRefinePrefix( TokenReference where, String fileName ) {
	super( where );
	this.fileName = fileName;
	levelNumber = JmlSourceClass.computeSuffixNumber(fileName);
    }

    //---------------------------------------------------------------------
    // ACCESSORS (quick)
    //---------------------------------------------------------------------

    public void setPackageName( String packageName ) {
	this.packageName = packageName;
    }

    public JCompilationUnitType refinedCUnit() {
	return refinedCUnit;
    }

    public String fileName() {
	return fileName;
    }

    //---------------------------------------------------------------------
    // DERIVED ATTRIBUTES
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // INTERFACE CHECKING
    //---------------------------------------------------------------------

    /**
     * Performs preliminary processing on compilation units and types.
     * Processes type imports so external methods' receiver types can
     * be analyzed and supertypes can be resolved.  Groups external
     * methods by name, corresponding to the anchor classes that will
     * eventually be generated.  Mutates the name space management in
     * CTopLevel to record a CGenericFunctionCollection singleton for
     * each anchor class.  */
    public void preprocessDependencies( org.multijava.mjc.Main compiler ) 
	throws PositionedError 
    {
	// fileName is a file name
	// System.out.println("PARSE REFINES " + fileName);

	fileName = packageName + fileName;

	String suffix = "";
	String prefix = "";
	int pos = fileName.lastIndexOf(".");
	if (pos >= 0) {
	    prefix = fileName.substring(0, pos);
	    suffix = fileName.substring(pos);
	}

	if (isClassFile()) {
	    // refines a ".class" file
	    refinedBinaryType = buildBinaryType( getTokenReference(), 
						 prefix );
	    return;
	}

	ClassPath.ClassDescription desc = ClassPath.getFile(prefix, suffix);
	if (desc == null)  {
	    // System.out.println("DESC NULL " + filename);
	    // no appropriate file exists to define the class

	    throw new PositionedError( getTokenReference(),
				       JmlMessages.REFINE_FILE_NOT_FOUND, 
				       fileName );
	} else {
	    // System.out.println("REFINE DESC SOURCE " + fileName);
	    File f = ((ClassPath.FileClassDescription) desc).file();
	    refinedCUnit = JmlTypeLoader.getJmlSingleton().getCUnitAST(f);
	    if (refinedCUnit == null) {
		refinedCUnit = ((Main)compiler).catchUpRefinedFile(f);
	    }
            if (refinedCUnit instanceof JmlCompilationUnit) {
                ((JmlCompilationUnit)refinedCUnit).setRefined();
            }

	    // System.out.println("After parse of REFINE File " + " " + fileName);
	}
    }

    public boolean isClassFile() {
	return (levelNumber == 9);
    }

    static public JmlBinaryType buildBinaryType( TokenReference where, 
						 String prefix ) 
	throws PositionedError 
    {
	String fileName = prefix + ".class";
	ClassPath.ClassDescription desc = ClassPath.getClassPathFile(prefix);
	if (desc == null)  {
	    // System.out.println("DESC NULL " + fileName );
	    // no appropriate file exists to define the class

	    throw new PositionedError( where, 
				       JmlMessages.REFINE_FILE_NOT_FOUND, 
				       fileName );
	}
	ClassPath.Data data = desc.getData();
	ClassInfo info;
	try {
	    info = new ClassInfo(data.getDataInput(), true);
	    data.release();
	} catch (ClassFileFormatException e) {
	    data.release();
	    e.printStackTrace();
	    info = null;
	} catch (IOException e) {
	    data.release();
	    e.printStackTrace();
	    info = null;
	}
	if (info != null) {
	    File f = info.sourceFile();
	    if (f == null) {
		f = new File(fileName);
	    }
	    JmlBinarySourceClass refinedBinaryClass 
		= new JmlBinarySourceClass( CTopLevel.getFromClassesCompiler(), 
					    info, f );

	    JmlBinaryType typ = new JmlBinaryType( where, 
						   refinedBinaryClass,
						   prefix );

	    return typ;
	} else {
	    throw new PositionedError( where, 
				       JmlMessages.REFINE_FILE_NOT_FOUND, 
				       fileName );
	}
    }

    public void checkLevelNumber( int prevLevel ) 
	throws PositionedError 
    {
	if ( -1 == levelNumber ) {
	    throw new PositionedError( getTokenReference(),
				       JmlMessages.INVALID_FILE_SUFFIX, 
				       fileName );
	}
    }

    public void preprocessRefinedTypes( JmlCompilationUnit surroundingCUnit ) 
	throws PositionedError 
    {
	if (surroundingCUnit == refinedCUnit) {
		// If we don't catch this self reference, then there are
		// attempts to refer to aspects of the data structure
		// before they have been computed, eventually leading to
		// a recursive reference that runs out of memory.
	    throw new PositionedError(getTokenReference(),
				      JmlMessages.INVALID_SELF_REFINEMENT,
				      fileName);
	}
	JTypeDeclarationType[] types = surroundingCUnit.typeDeclarations();

	if (refinedBinaryType != null) {
	    // The refined file is a binary .class file
	    for( int i = 0; i < types.length; i++ ) {
		if( types[i] instanceof JmlTypeDeclaration ) {
		    JmlTypeDeclaration typeDecl = (JmlTypeDeclaration)types[i];
		    if( typeDecl.ident().equals(refinedBinaryType.ident()) ) {
			typeDecl.setRefinedType(refinedBinaryType);
		    }
		} else {
		    // !FIXME! probably an error: should be a JmlTypeDeclaration
		    // should probably throw an exception here since 
		    // the AST was not properly built
		}
	    } 
	} else {
	    // The refined file is a compilation unit
	    JmlTypeDeclaration typeDecl;
	    JTypeDeclarationType[] refinedTypes;
	    JmlTypeDeclaration refinedDecl;

	    for( int i = 0; i < types.length; i++ ) {
		if( types[i] instanceof JmlTypeDeclaration ) {
		    typeDecl = (JmlTypeDeclaration)types[i];
		    if (refinedCUnit != null) {
			refinedTypes = refinedCUnit.typeDeclarations();
			for( int j = 0; j < refinedTypes.length; j++ ) {
			    if(typeDecl.ident().equals(
					refinedTypes[j].ident())) {
				refinedDecl = (JmlTypeDeclaration) refinedTypes[j];
				typeDecl.setRefinedType(refinedDecl);
			    }
			}
		    } 
		} else {
		    // !FIXME! probably an error: should be a JmlTypeDeclaration
		    // should probably throw an exception here since 
		    // the AST was not properly built
		}
	    }
	}
    }

    //---------------------------------------------------------------------
    // TYPECHECKING
    //---------------------------------------------------------------------

    public void checkInterface() 
	throws PositionedError 
    {
	if ( refinedCUnit instanceof JmlCompilationUnit ) {
	    JmlTypeLoader.getJmlSingleton()
		.activatePartiallyProcessedTask( 
				(JmlCompilationUnit)refinedCUnit );
	}
    }
    


    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    /**
     * Accepts the specified visitor.
     * @param p	the visitor
     */
    public void accept( MjcVisitor p ) {
	if (p instanceof JmlVisitor)
	    ((JmlVisitor)p).visitJmlRefinePrefix(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVATE DATA MEMBERS
    //---------------------------------------------------------------------

    private String fileName;
    private String packageName = "";

    /**
     *  The parsed compilation unit referenced by <code>fileName</code>
     */
    private JCompilationUnitType refinedCUnit = null;

    /**
     *  The interface of the ".class" file referenced by <code>fileName</code>
     */
    private JmlBinaryType refinedBinaryType = null;

    //---------------------------------------------------------------------
    // PROTECTED DATA MEMBERS
    //---------------------------------------------------------------------

    /** 
     *  See {@link JmlSourceClass} for an explanation of 
     *  the levelNumber field
     */
    protected int levelNumber = -1;
}
