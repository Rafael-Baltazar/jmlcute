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
 * $Id: JmlDataGroupMemberMap.java,v 1.5 2004/03/21 19:02:50 davidcok Exp $
 */

package org.jmlspecs.checker;

import org.multijava.mjc.CField;

import java.util.Iterator;
import java.util.HashMap;

/**
 * This class acts as a 
 */
public class JmlDataGroupMemberMap {
    // ----------------------------------------------------------------------
    // CONSTRUCTORS
    // ----------------------------------------------------------------------

    public JmlDataGroupMemberMap() {
	memberMap = new HashMap();
    }

    /**
     * Add a mapping from <code>field</code> to the members 
     * of its data group.  Initially the member set only has 
     * one member, i.e., <code>field</code>.  This is only 
     * done if <code>field</code> is a data group, i.e., if it 
     * is a model field or has either a spec_public or spec_protected 
     * visibility modifier.
     */
    public void addGroup( JmlSourceField field ) {
	if ( field.isDataGroup() ) {
	    field = field.getMostRefined();
	    JmlAssignableFieldSet fldSet = getMembers( field );
	    if ( fldSet == null ) {
		memberMap.put( field, new JmlAssignableFieldSet(field) );
	    }
	}
    }

    /**
     * Add <code>member</code> to the member set of <code>group</code> 
     * if <code>group</code> is already in this map. 
     * Otherwise, create a new group and add <code>member</code> 
     * to the member set for <code>group</code>. 
     *
     * <pre><jml>
     * requires group != null &&  member != null && group.isDataGroup();
     * </jml></pre>
     */
    public void addMember( JmlSourceField group, CField member ) {
	if ( ! group.isDataGroup() ) {
	    System.err.println("The field " + group.ident() 
			       + " is not a data group");
	    return;
	}
	group = group.getMostRefined();
	if ( !memberMap.containsKey(group) ) {
	    addGroup(group);
	    addMember(group, member);
	}
	JmlAssignableFieldSet fldSet = getMembers(group);
	fldSet.add(member);
    }

    /**
     * Add a mapping for <code>group</code> if it is not already in this 
     * map. Otherwise, merge (union) <code>member</code> with 
     * sets for any groups that are in both maps.
     *
     * <pre><jml>
     * requires group != null &&  members != null && group.isDataGroup();
     * </jml></pre>
     */
    public void addMembers( JmlSourceField group, 
			    JmlAssignableFieldSet members )
    {
	if ( ! group.isDataGroup() ) {
	    System.err.println("The field " + group.ident() 
			       + " is not a data group");
	    return;
	}
	group = group.getMostRefined();
	JmlAssignableFieldSet fldSet = getMembers(group);
	if ( fldSet == null ) {
	    memberMap.put(group, members.clone());
	} else {
	    Iterator iter = members.iterator();
	    while ( iter.hasNext() ) {
		fldSet.add( (JmlSourceField)iter.next() );
	    }
	}
    }

    public Iterator keyGroupIterator() {
	return memberMap.keySet().iterator();
    }

    /**
     * Add mappings for any groups in <code>parentMap</code> that are 
     * already in this map. Also, merge (union) the member sets for any 
     * groups that are in both maps.
     *
     * <pre><jml>
     * requires parentMap != null && inheritedMembersAdded == false;
     * </jml></pre>
     */
    public void addInheritedMembers( JmlDataGroupMemberMap parentMap )
    {
	if ( inheritedMembersAdded ) {
	    System.err.println("The inherited members of the data group have already been added");
	    return;
	}
	Iterator groupIter = parentMap.keyGroupIterator();
	while ( groupIter.hasNext() ) {
	    JmlSourceField group = (JmlSourceField)groupIter.next();
	    JmlAssignableFieldSet fldSet = parentMap.getMembers(group);
	    this.addMembers( group, fldSet );
	}
	inheritedMembersAdded = true;
    }

    /**
     * Returns the members of the given data group. 
     * If <code>group</code> is not in the domain of this map, 
     * then null is returned.
     *
     * <pre><jml>
     * requires group != null;
     * </jml></pre>
     */
    public JmlAssignableFieldSet getMembers( JmlSourceField group ) {
	return (JmlAssignableFieldSet) memberMap.get( group );
    }

    //@ also modifies objectState;
    public String toString() {
	String strOut = "{";
	Iterator iter = memberMap.keySet().iterator();
	while ( iter.hasNext() ) {
	    strOut += "(";
	    JmlSourceField fld = (JmlSourceField) iter.next();
	    strOut += fld.ident() + " -> ";
	    strOut += memberMap.get(fld).toString();
	    strOut += "),\n";
	}
	return strOut + "}";
    }

    /** A mapping from <code>JmlSourceField</code> objects to 
     *  <code>JmlAssignableFieldsSet</code> objects for handling members 
     * of data groups and checking assignable clauses.   
     *
     * <pre><jml>
     * private invariant memberMap != null;
     * </jml></pre>
     */
    private HashMap memberMap;

    private /*@ spec_public @*/ boolean inheritedMembersAdded = false;
}
