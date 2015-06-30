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
 * $Id: JmlClassBlock.java,v 1.5 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.MjcVisitor;
import org.multijava.mjc.JClassBlock;
import org.multijava.mjc.JStatement;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.CMethod;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.PositionedError;
import org.multijava.javadoc.JavadocComment;

/**
 * This class represents a instance or static initializer block annotated
 * with a JML method specification.
 *
 * @author Curtis Clifton
 * @version $Revision: 1.5 $
 */

public class JmlClassBlock extends JClassBlock {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------


    /**
     * Constructs an initializer specification AST node.
     *
     *
     * <pre><jml>
     * {|
     *   requires isStatic;
     *   ensures (* this represents a 
     *		    method-specification "static_initializer" member *);
     * also
     *   requires !isStatic;
     *   ensures (* this represents a 
     *		    method-specification "initializer" member *);
	 * |}
     * </jml></pre>
     *
     */
    public JmlClassBlock( TokenReference where, boolean isStatic,
			  JavadocComment javadoc, 
			  JmlMethodSpecification methodSpecification ) {
	super( where, isStatic, new JStatement[0], javadoc );
	this.methodSpecification = methodSpecification;
    }
    
    /**
     * Constructs an initializer AST node annotated with a method 
     * specification.
     *
     *
     * <pre><jml>
     * {|
     *   requires isStatic;
     *   ensures (* this represents a 
     *		    method-specification static { ... } member *);
     * also
     *   requires !isStatic;
     *   ensures (* this represents a 
     *		    method-specification { ... } member *);
	 * |}
     * </jml></pre>
     *
     */
    public JmlClassBlock( TokenReference where, boolean isStatic,
			  JStatement[] body, JavadocComment javadoc, 
			  JmlMethodSpecification methodSpecification ) {
	super( where, isStatic, body, javadoc );
	this.methodSpecification = methodSpecification;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public boolean hasSpecification() {
	return methodSpecification != null;
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
     * Typechecks this initializer in the context in which it
     * appears.  Mutates the context to record the information learned
     * during checking.
     *
     * @param context	the context in which this appears
     * @exception PositionedError if any checks fail */
    public void typecheck( CFlowControlContextType context ) 
	throws PositionedError 
    {
	super.typecheck( context );
	if (methodSpecification != null) {
	    CMethod meth = context.getCMethod();
	    long mods = meth.modifiers();
	    mods = (mods & ~ACC_PRIVATE) | ACC_PUBLIC;
	    meth.setModifiers(mods);
	    methodSpecification.typecheck( context );
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
	    ((JmlVisitor)p).visitJmlClassBlock(this);
	else
	    throw new UnsupportedOperationException(JmlNode.MJCVISIT_MESSAGE);
    }

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    private JmlMethodSpecification methodSpecification;

}// JmlClassBlock
