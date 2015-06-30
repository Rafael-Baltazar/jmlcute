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
 * $Id: JmlDataGroupAccumulator.java,v 1.5 2003/09/08 15:31:54 cclifton Exp $
 */

package org.jmlspecs.checker;

import java.util.ArrayList;
import java.util.Iterator;


/**
 * This class represents a set of jml-data-group-assertion's in JML ASTs.
 *
 * @author Clyde Ruby
 * @version $Revision: 1.5 $
 */

public class JmlDataGroupAccumulator 
{

    //---------------------------------------------------------------------
    // CONSTRUCTORS 
    //---------------------------------------------------------------------

    public JmlDataGroupAccumulator() {
	inGroupList = new ArrayList(5);
	mapsIntoList = new ArrayList(5);
    }
    
    //---------------------------------------------------------------------
    // ACCESSORS
    //---------------------------------------------------------------------

    public void addInGroup( JmlInGroupClause fieldAssertion ) {
	inGroupList.add( fieldAssertion );
    }

    public JmlInGroupClause[] inGroupClauses() {
	if (inGroups == null) {
	    inGroups = new JmlInGroupClause[ inGroupList.size() ];
	    inGroupList.toArray( inGroups );
	    inGroupList = null;
	}
	return inGroups;
    }

    public void addMapsInto( JmlMapsIntoClause fieldAssertion ) {
	mapsIntoList.add( fieldAssertion );
    }

    public ArrayList mapsIntoClauses() {
	return mapsIntoList;
    }

    public JmlMapsIntoClause[] getMapsIntoClausesFor( String fieldId ) {
	ArrayList resultList = new ArrayList(mapsIntoList.size());
	Iterator iter = mapsIntoList.iterator();
	while (iter.hasNext()) {
	    JmlMapsIntoClause nextClause = (JmlMapsIntoClause) iter.next();
	    if ( nextClause.fieldIdent().equals(fieldId) ) {
		resultList.add(nextClause);
		iter.remove();
	    }
	}

	JmlMapsIntoClause[] result = new JmlMapsIntoClause[resultList.size()];
	resultList.toArray(result);
	
	return result;
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

    //---------------------------------------------------------------------
    // CODE GENERATION
    //---------------------------------------------------------------------

    //---------------------------------------------------------------------
    // PRIVILEGED DATA
    //---------------------------------------------------------------------
    protected ArrayList inGroupList;
    protected ArrayList mapsIntoList;

    protected JmlInGroupClause[] inGroups = null;

}// JmlDataGroupAccumulator
