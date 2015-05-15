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
 * $Id: JmlDataGroupClause.java,v 1.8 2005/04/26 02:40:16 kui_dai Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CExpressionContext;
import org.multijava.mjc.CExpressionContextType;
import org.multijava.mjc.CFieldAccessor;
import org.multijava.mjc.CFlowControlContextType;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JExpression;
import org.multijava.util.compiler.PositionedError;
import org.multijava.util.compiler.TokenReference;
import org.multijava.util.compiler.UnpositionedError;

/**
 * This class represents a jml-var-assertion of the form <code>initially</code>
 * <em>predicate</em>.
 *
 * @author Clyde Ruby
 * @version $Revision: 1.8 $
 */

public abstract class JmlDataGroupClause extends JmlNode implements Cloneable {

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------
    public JmlDataGroupClause( TokenReference where,
			       boolean redundantly, 
			       JmlStoreRefExpression[] groupList )
    {
	super( where );
	this.redundantly = redundantly;
	this.groupList = groupList;
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    /*
     * Clones this, making a deep copy of any mutable state.
     * Overrides the superclass method, eliminating the
     * <code>CloneNotSupportedException</code>, thus forcing all
     * subclasses to be clonable.  
     */
    public Object clone() {
	try {
	    return super.clone();
	} catch (CloneNotSupportedException e) {
	    // Superclass should be clonable. It declares
	    // CloneNotSupportedException so that subclasses can
	    // choose to not be clonable.

	    //@ unreachable; 

	    return null;
	}
    }

    public /*@ pure @*/ boolean isRedundantly() {
	return redundantly;
    }

    public JmlStoreRefExpression[] groupList() {
	return groupList;
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
     * Typecheck this variable assertion and mutates the context to
     * store the information obtained during the checking.
     *
     * @param context the context in which this var assertion is declared
     * @exception PositionedError if any checks fail 
     */
    public void typecheck( CFlowControlContextType context, long privacy )
	throws PositionedError 
    {
	try {
	    enterSpecScope();
	    JmlExpressionContext ectx =
		JmlExpressionContext.createIntracondition( context );

	    groups = new JmlSourceField[groupList.length];

	    for (int i = 0; i < groupList.length; i++) {
		// This try block allows display of errors for more than 
		// one id in the list
		try {
		    groupList[i] = (JmlStoreRefExpression) 
			groupList[i].typecheck( ectx, ACC_PRIVATE );

		    // We use private visibility above so the group names are 
		    // resolved without a visibility error.  However, 
		    // the visibility is checked in "checkDataGroup" below.

		    String ident = groupList[i].getName();
		    groups[i] = checkDataGroup(context, 
					       groupList[i].expression(), 
					       ident, privacy );
		} catch (PositionedError e) {
		    context.reportTrouble(e);
		}
	    }
	}
	finally {
	    exitSpecScope();
	}
    }
    public JmlSourceField checkDataGroup( CFlowControlContextType context, 
					  JExpression groupNameExpr,
					  String ident, long privacy )
    {
	JmlSourceField result = null;

	if (groupNameExpr instanceof JClassFieldExpression) {
	    CFieldAccessor field 
		= ((JClassFieldExpression)groupNameExpr).getField();
	    if ( field instanceof JmlSourceField ) {
		if ( ((JmlSourceField)field).isDataGroup() ) {
		    // OK
		    result = (JmlSourceField) field;
		} else {
		    context.reportTrouble(
			new PositionedError( groupNameExpr.getTokenReference(),
					     JmlMessages.DATA_GROUP_NOT_MODEL,
					     ident )
			);
		}
		JmlMemberAccess fldAccess 
		    = ((JmlSourceField) field).jmlAccess();
		if ( !JmlExpressionChecker
		     .isVisibilityOk(privacy, fldAccess.modifiers()) ) {
		    context.reportTrouble(
			new PositionedError( groupNameExpr.getTokenReference(),
					     JmlMessages.DATA_GROUP_VISIBILITY,
					     ident )
			);
		    result = null;
		}
	    }
	} else {
	    context.reportTrouble(
			new PositionedError( groupNameExpr.getTokenReference(),
					     JmlMessages.DATA_GROUP_NOT_MODEL,
					     ident )
			);
	}
	return result;
    }

    public JmlSourceField[] getDataGroups(  JmlSourceField self ) {
	if ( groups == null ) {
	    // When the associated field declaration has not yet been 
	    // typechecked.  This also happens when handling data 
	    // groups inherited from the super class or implemented 
	    // interfaces that are not going to be fully typechecked.

	    JmlSourceClass fieldOwner = (JmlSourceClass) self.owner();
	    groups = new JmlSourceField[groupList.length];
	    CExpressionContextType dummyContext 
		= new CExpressionContext( 
		      JmlContext.createDummyContext(fieldOwner) );

	    for (int i=0; i<groupList.length; i++) {
		try {
		    // data groups are model fields
		    JmlContext.enterSpecScope();

		    JmlName[] names = groupList[i].names();
		    String name = names[0].ident();
		    if (names.length > 1) {
			fieldOwner 
			    = (JmlSourceClass) fieldOwner.getSuperClass();
			name = names[1].ident();
		    }
		    groups[i] = (JmlSourceField)
			fieldOwner.lookupFieldHelper(name, dummyContext);
		} catch (UnpositionedError e) {
		    dummyContext.reportTrouble(
			new PositionedError( 
			        groupList[i].getTokenReference(),
			        e.getFormattedMessage() )
			);
		    groups[i] = null;
		}
		finally{
		    JmlContext.exitSpecScope();
		}
	    }
	}
	return groups;
    }

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------

    protected /*@ non_null @*/ JmlStoreRefExpression[] groupList;

    protected JmlSourceField[] groups;

    /**
     * Indicates whether this is a redundant annotation.  */
    protected final boolean redundantly;

}// JmlDataGroupClause
