/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * based in part on work:
 *
 * Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
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
 * $Id: JmlAssignableFieldSet.java,v 1.13 2005/07/11 21:28:15 leavens Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;

import org.multijava.mjc.CField;
import org.multijava.mjc.JClassFieldExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JThisExpression;

/**
 *  This class acts as a set containing the assignable fields mentioned 
 *  in an assignable clause.   
 *  This class is also used to accumulate the members (fields) of a data group.
 */
public class JmlAssignableFieldSet {

    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    public JmlAssignableFieldSet() {
	containsEverything = false;
	notSpecified = false;
	containsPrivateFields = false;
	theFieldSet = new LinkedHashSet(16);
	dataGroupList = new ArrayList(16);
    }

    public JmlAssignableFieldSet( CField field ) {
	containsEverything = false;
	notSpecified = false;
	containsPrivateFields = false;
	theFieldSet = new LinkedHashSet(16);
	dataGroupList = new ArrayList(16);
	this.add( field );
    }

    private JmlAssignableFieldSet( JmlAssignableFieldSet other )
    {
	this.containsEverything = other.containsEverything;
	this.notSpecified = other.notSpecified;
	this.containsPrivateFields = other.containsPrivateFields;
	this.containsDynamicFields = other.containsDynamicFields;
	this.theFieldSet = (LinkedHashSet) other.theFieldSet.clone();
	this.dataGroupList = (ArrayList) other.dataGroupList.clone();
    }

    public boolean add( CField field ) {
	if ( containsEverything ) {
	    // no need to add to theFieldSet.
	    return true;
	} else {
	    if ( field instanceof JmlSourceField ) {
		JmlSourceField member = (JmlSourceField) field;
		member = member.getMostRefined();
		if ( member.isDataGroup() ) {
		    // data group members are added to both the field set 
		    // and the data group list.
		    return theFieldSet.add( member )
			&& dataGroupList.add( member );
		}
	    }
	}
	return theFieldSet.add( field );
    }

    public boolean add( JmlStoreRef storeRef ) {
	if ( storeRef.isNotSpecified() ) {
	    this.notSpecified = true;
	    return true;
	} else if ( storeRef.isEverything() ) {
	    this.containsEverything = true;
	    return true;
	} else if ( storeRef.isPrivateData() ) {
	    this.containsPrivateFields = true;
	    return true;
	} else if ( storeRef.isStoreRefExpression() ) {
	    JmlStoreRefExpression storeRefExpr 
		= (JmlStoreRefExpression) storeRef;
	    CField field = (CField) storeRefExpr.getField();
	    if ( storeRefExpr.isFieldOfReceiver() ) {
		if (field != null) {
		    // type checking did not fail
		    return this.add( field );
		}
		return false;
	    } else {
		// !FIXME! skip qualified names for now
		this.containsDynamicFields = true;
		return false;
	    }

	} else if ( storeRef.isInformalStoreRef() ) {
	    this.notSpecified = true;
	    return true;
	} else {
	    // \nothing 
	    // So no fields should be added to theFieldSet.
	    return true;
	}
    }

    public void clear() {
	containsEverything = false;
	notSpecified = false;
	containsPrivateFields = false;
	theFieldSet.clear();
	dataGroupList.clear();
    }

    public /*@ pure @*/ Object clone() {
	return new JmlAssignableFieldSet( this );
    }

    public boolean contains( CField field ) {
	if ( this.isUniversalSet() ) {
	    return true;
	} else if ( containsPrivateFields && field.isPrivate() ) {

	    // Not completely general.  Need the owner in general, 
	    // but this method is only called in the context 
	    // where the method owner would be the same as the 
	    // field owner (since the field is private).

	    return true;
	} else {
	    if ( field instanceof JmlSourceField ) {
		field = ((JmlSourceField)field).getMostRefined();
	    }
	    return theFieldSet.contains(field);
	}
    }

    public void setNotSpecified() {
	notSpecified = true;
    }

    public boolean contains( CField field, JmlDataGroupMemberMap dgMap )
    {
	if ( this.contains(field) ) {
	    return true;
	}
	Iterator dgIter = dataGroupList.iterator();
	while ( dgIter.hasNext() ) {
	    JmlSourceField grp = (JmlSourceField) dgIter.next();
	    JmlAssignableFieldSet memberSet = dgMap.getMembers( grp );
	    if ( memberSet != null && memberSet != this ) {
		if ( memberSet.contains(field, dgMap) ) {
		    return true;
		}
	    }
	}
	return false;
    }

    public boolean contains( JClassFieldExpression fieldExpr, 
			     JmlDataGroupMemberMap dgMap )
		
    {
	if ( this.isUniversalSet() ) {
	    return true;
	}
	JExpression prefix = fieldExpr.prefix();
	if (prefix instanceof JThisExpression) {
	    CField field = fieldExpr.getField().getField();
	    return contains(field, dgMap);
	} else {
	    // !FIXME!
	    // don't try to match fields of other objects
	    // because we don't yet handle dynamic dependencies!
	    return true;
	}
    }

    public /*@ pure @*/ int size() {
	return theFieldSet.size();
    }

    public /*@ pure @*/ Iterator iterator() {
	return theFieldSet.iterator();
    }

    public /*@ pure @*/ boolean isEmpty() {
	return !isUniversalSet() && size() == 0 && !containsDynamicFields;
    }

    public /*@ pure @*/ boolean isUniversalSet() {
	return notSpecified || containsEverything;
    }

    public /*@ pure @*/ boolean isNotSpecified() {
	return notSpecified && size() == 0 && !containsEverything;
    }

    public boolean addAll( JmlAssignableFieldSet otherSet ) {
	if ( otherSet == null ) {
	    // when null it means that the other set was unspecified
	    this.notSpecified = true;
	    return false;
	} 
	this.containsEverything |= otherSet.containsEverything;
	this.notSpecified |= otherSet.notSpecified;
	this.containsPrivateFields |= otherSet.containsPrivateFields;
	this.containsDynamicFields |= otherSet.containsDynamicFields;
	Iterator iter = otherSet.iterator();
	while ( iter.hasNext() ) {
	    this.add( (CField) iter.next() );
	}
	return true;
    }

    public boolean isSubsetOf( JmlAssignableFieldSet otherSet, 
			       JmlDataGroupMemberMap dgMap ) 
    {
	if ( this.isUniversalSet() ) {
	    return otherSet.isUniversalSet();
	} else if ( otherSet.isUniversalSet() ) {
	    return true;
	} else {
	    Iterator iter = this.iterator();
	    while ( iter.hasNext() ) {
		if ( ! otherSet.contains((CField)iter.next(), dgMap) ) {
		    return false;
		}
	    }
	}
	return true;
    }

    public boolean isSupersetOf( JmlAssignableFieldSet otherSet,
				 JmlDataGroupMemberMap dgMap ) 
    {
	return otherSet.isSubsetOf( this, dgMap );
    }

    public JmlAssignableFieldSet intersect( JmlAssignableFieldSet otherSet,
					    JmlDataGroupMemberMap dgMap ) 
    {
	if (otherSet == null) {
	    return (JmlAssignableFieldSet) this.clone();
	} else if ( this.isUniversalSet() ) {
	    return (JmlAssignableFieldSet) otherSet.clone();
	} else if ( otherSet.isUniversalSet() ) {
	    return (JmlAssignableFieldSet) this.clone();
	} else {
	    JmlAssignableFieldSet result = new JmlAssignableFieldSet();
	    Iterator iter = this.iterator();
	    while ( iter.hasNext() ) {
		CField field = (CField) iter.next();
		if ( otherSet.contains(field, dgMap) ) {
		    result.add(field);
		}
	    }
	    return result;
	}
    }

    public /*@ pure @*/ String toString() {
	CField fld;
	String strOut = "{";
	Iterator iter = this.iterator();
	if (containsEverything) {
	    strOut += "\\everything";
	    if (notSpecified) {
		strOut += ", \\not_specified";
	    }
	} else if (notSpecified) {
	    strOut += "\\not_specified";
	} else {
	    if ( iter.hasNext() ) {
		fld = (CField) iter.next();
		strOut += fld.ident();
	    }
	}
	while ( iter.hasNext() ) {
	    fld = (CField) iter.next();
	    strOut += ", " + fld.ident();
	}
	strOut += "}";
	return strOut;
    }

    // ---------------------------------------------------------------------- 
    // PRIVILEGED DATA MEMBERS
    // ----------------------------------------------------------------------

    /** A set containing all the fields in this data group.
     *  Also used to accumulate the assignable fields mentioned 
     *  in an assignable clause.   
     *
     * <pre><jml>
     * invariant theFieldSet != null;
     * </jml></pre>
     */
    private /*@ spec_public @*/ LinkedHashSet theFieldSet;

    /** A list containing only the fields that have an associated data group.
     *
     * <pre><jml>
     * invariant dataGroupList != null;
     * </jml></pre>
     */
    private /*@ spec_public @*/ ArrayList dataGroupList;

    private boolean containsEverything = false;
    private boolean notSpecified = false;
    private boolean containsPrivateFields = false;
    private boolean containsDynamicFields = false;

}
