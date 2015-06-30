/*
 * Copyright (C) 2002 Iowa State University
 *
 * This file is part of jml, type checker for the Java Modeling Language.
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
 * $Id: JmlSourceField.java,v 1.15 2003/12/21 03:51:37 davidcok Exp $
 */

package org.jmlspecs.checker;

import org.jmlspecs.util.classfile.JmlFieldInfo;
import org.jmlspecs.util.classfile.JmlModifiable;
import org.multijava.mjc.CField;
import org.multijava.mjc.CMemberHost;
import org.multijava.mjc.CSourceField;
import org.multijava.mjc.CType;
import org.multijava.util.classfile.FieldInfo;

/**
 * A class for representing an exported field of a class.
 * This class provides JML-specific handling of fields by overriding 
 * several inherited methods. For example, the visibility observer 
 * methods such as <code>isPublic</code>, <code>isProtected</code>, and 
 * <code>isPrivate</code> now consider spec_public-ness and 
 * spec_protected-ness too.
 *
 * @author Yoonsik Cheon
 * @version $Revision: 1.15 $
 */
public class JmlSourceField extends CSourceField 
    implements JmlModifiable, Constants
{

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    /**
     * Constructs a field export
     * @param	access		contains the info used to determine visibility of this field
     * @param	ident		the name of this field
     * @param	type		the type of this field
     * @param	deprecated	is this field deprecated
     */
    public JmlSourceField(JmlMemberAccess access, String ident, 
			  CType type, boolean deprecated) 
    {
	super(access, ident, type, deprecated);
        // model fields are assumed to be initialized.
        // !FIXME!05/08! maybe always assume initialized?
        if (access.isModel()) {
            initializedUnlessFinalInstance();
        }
    }


    // ----------------------------------------------------------------------
    // TYPE CHECKING
    // ----------------------------------------------------------------------

    /**
     * Returns true if this member has an associated data group.
     * That is, model fields and spec_public and spec_protected 
     * have associated data groups.  
     */
    public /*@ pure @*/ boolean isDataGroup() {
	JmlMemberAccess access = jmlAccess();
	return ( access.isModel() || access.isSpecPublic() 
		 || access.isPublic() || access.isProtected()
		 || access.isSpecProtected() );
    }

    /**
     *
     */
    public boolean isDefinitelyAssigned() {
	// if this field is final and not in a '.java' file 
	// or if it's a model field then we assume it is 
	// assigned to.  The check will only be done for a 
	// declaration occurring in the '.java' file.
	if ( (isFinal() && !inJavaFile()) || jmlAccess().isModel() ) {
	    return true;
	}
	return super.isDefinitelyAssigned();
    }

    /**
     * Returns true if this member is declared in a '.java' file.
     */
    public boolean inJavaFile() {
	return jmlAccess().inJavaFile();
    }

    /**
     * Returns true iff this field should be treated as a model field;
     * the field itself is defined as model (or ghost) or it is defined in a 
     * model class or interface.
     */
    public /*@ pure @*/ boolean isEffectivelyModel() {
	return jmlAccess().isModel()
	    || jmlAccess().isGhost()
	    || (owner() != null 
		&& ((JmlSourceClass)owner()).isEffectivelyModel());
    }

    /**
     * Returns true iff this field is explicitly declared as model.
     */
    public /*@ pure @*/ boolean isModel() {
	return jmlAccess().isModel();
    }

    /**
     * Returns true iff this field is explicitly declared as ghost.
     */
    public /*@ pure @*/ boolean isGhost() {
	return jmlAccess().isGhost();
    }

    /** 
     */
    public boolean isLocalTo( CMemberHost from ) {
	if ( super.isLocalTo( from ) ) {
	    return true;
	} else if (from instanceof JmlSourceClass) {
	    CMemberHost myHost = host();
	    JmlSourceClass fromClass = (JmlSourceClass) from;
	    return fromClass.refines(myHost);
	}
	return false;
    }

    /**
     * Sets the AST for this field.
     */
    public void setAST(JmlMemberDeclaration fieldAST) 
    {
	this.fieldAST = fieldAST;
    }

    /**
     * Returns the AST for this field.
     */
    public JmlMemberDeclaration getAST() {
	return fieldAST;
    }

    /**
     * Returns the most refined declaration AST for this field.
     */
    public JmlSourceField getMostRefined() {
	CField mostRefinedDecl = fieldAST.getMostRefined().getField();
	return (JmlSourceField) mostRefinedDecl;
    }

    /**
     * @return	the member access information object for this member.
     */
    public /*@ pure @*/ JmlMemberAccess jmlAccess() {
        return (JmlMemberAccess) access();
    }

    // ----------------------------------------------------------------------
    // CODE GENERATION
    // ----------------------------------------------------------------------

    /**
     * Creates a new field info object. This method is overridden here to
     * return a JML-specific field info object.
     */
    protected FieldInfo createFieldInfo(int modifiers,
                                        String name,
                                        String type,
                                        Object value,
                                        boolean deprecated,
                                        boolean synthetic) {
        return new JmlFieldInfo(modifiers, name, type, value, deprecated, 
                                synthetic);
    }

    // ----------------------------------------------------------------------
    // DATA MEMBERS
    // ----------------------------------------------------------------------
    
    private JmlMemberDeclaration fieldAST = null;
}
