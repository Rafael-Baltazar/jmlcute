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
 * $Id: NonNullStatistics.java,v 1.23 2006/11/27 15:36:48 perryjames Exp $
 */

package org.jmlspecs.checker;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;
import java.util.Vector;

import org.multijava.mjc.CClass;
import org.multijava.mjc.CMethod;
import org.multijava.mjc.CMethodSet;
import org.multijava.mjc.JBitwiseExpression;
import org.multijava.mjc.JBooleanLiteral;
import org.multijava.mjc.JConditionalAndExpression;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFormalParameter;
import org.multijava.mjc.JInstanceofExpression;
import org.multijava.mjc.JMethodDeclaration;
import org.multijava.mjc.JNameExpression;
import org.multijava.mjc.JNullLiteral;
import org.multijava.mjc.JParenthesedExpression;
import org.multijava.mjc.JThisExpression;
import org.multijava.mjc.JUnaryExpression;
import org.multijava.util.Utils;
import org.multijava.util.compiler.PositionedError;

public class NonNullStatistics implements Constants {
    public NonNullStatistics(File[] files){
	hmArgs= new HashMap(files.length);
	hmNonnull= new HashMap(files.length*5);
	hmNnStat= new HashMap(files.length*5);
	hmSpecCase= new HashMap(files.length*5);
	hmSuperSpec = new HashMap(files.length*5);
	strArgs = new String[files.length]; //store all command line fil names
	stackSpecCase = new Stack();
	stackValue = new Stack();
	currMethod="";
	currClass="";
	for (int i=0; i<files.length; i++) {
	    String key = Utils.getFilePath( files[i] );	    
	    //create hashmap for non_null stat,                                          
	    //0-normal class field decl with nn,
	    //1-method decl with nn,
	    //2-para decl with nn             
	    //3-class decl sum
	    //4-method decl sum
	    //5-para decl sum
	    //6-sum of !=null in requires                            
	    //6- also for ensures
	    //8-sum of !=null in invariant
	    //9--sum of !=null in \result                             
	    int[] v = new int[30];
	    strArgs[i]= key;
	    hmArgs.put(key,v);
	    //System.out.println("key is "+key);
	}
    }

    public static void outPutStat(){

	    System.out.println("File\tField\tModelField\tGhostField\tMethod\tModelMethod\tParam\tModelParam");

	    Iterator it = hmNonnull.keySet().iterator();
	    while (it.hasNext()){
		String key = (String)it.next();
		String value = (String)hmNonnull.get(key);
		String s = key.substring(0,key.indexOf("|"));

       		if ("Mm".equals(value)){
		    ((int[])hmArgs.get(s))[0]++;
		} else if ("Rm".equals(value)){
		    ((int[])hmArgs.get(s))[1]++;
		} else if ("mm".equals(value)){
		    ((int[])hmArgs.get(s))[2]++;
		} else if ("rm".equals(value)){
		    ((int[])hmArgs.get(s))[3]++;
		} else if ("Gf".equals(value)){
		    ((int[])hmArgs.get(s))[4]++;
		} else if ("Mf".equals(value)){
		    ((int[])hmArgs.get(s))[5]++;
		} else if ("Rf".equals(value)){
		    ((int[])hmArgs.get(s))[6]++;
		} else if ("gf".equals(value) || "gs".equals(value)){
		    ((int[])hmArgs.get(s))[7]++;
		} else if ("mf".equals(value) || "ms".equals(value)){
		    ((int[])hmArgs.get(s))[8]++;
		} else if ("rf".equals(value) || "rs".equals(value)){
		    ((int[])hmArgs.get(s))[9]++;
		} else if ("Mp".equals(value)){
		    ((int[])hmArgs.get(s))[10]++;
		} else if ("Rp".equals(value)){
		    ((int[])hmArgs.get(s))[11]++;
		} else if ("mp".equals(value)){
		    ((int[])hmArgs.get(s))[12]++;
		} else if ("rp".equals(value)){
		    ((int[])hmArgs.get(s))[13]++;
		}

		if (hmNnStat.containsKey(key)){//spec contains key
		    String valueSpec = (String) hmNnStat.get(key);

		    char c = value.charAt(0);
		    if (c=='m'){//model
			if (valueSpec.compareTo("Nm")==0){//result, method decl
			    ((int[])hmArgs.get(s))[14]++;//Mm
			} else if (valueSpec.compareTo("Nf")==0){//invariant, class field
			    ((int[])hmArgs.get(s))[15]++;//Mf
			} else if (valueSpec.compareTo("Np")==0){//parameter
			    ((int[])hmArgs.get(s))[16]++;//Mp
			}
		    }else if (c=='g'){//ghost
			if (valueSpec.compareTo("Nf")==0){//Invariant, class field
			    ((int[])hmArgs.get(s))[17]++;//Gf
			}
		    }else if (c=='r'){//reference
			if (valueSpec.compareTo("Nm")==0){//result, method decl
			    ((int[])hmArgs.get(s))[18]++;//Rm
			} else if (valueSpec.compareTo("Nf")==0){//invariant, class field
			    ((int[])hmArgs.get(s))[19]++;//Rf
			} else if (valueSpec.compareTo("Np")==0){//parameter 
			    ((int[])hmArgs.get(s))[20]++;//Rp
			}
		    }else if (c=='M'){//model, both
			if (valueSpec.compareTo("Nm")==0){//result, method decl
			    ((int[])hmArgs.get(s))[21]++;//Mm
			} else if (valueSpec.compareTo("Nf")==0){//invariant, class field
			    ((int[])hmArgs.get(s))[22]++;//Mf
			} else if (valueSpec.compareTo("Np")==0){//parameter
			    ((int[])hmArgs.get(s))[23]++;//Mp
			}
		    }else if (c=='G'){//ghost
			if (valueSpec.compareTo("Nf")==0){//Invariant, class field
			    ((int[])hmArgs.get(s))[24]++;//Gf
			}
		    }else if (c=='R'){//reference
			if (valueSpec.compareTo("Nm")==0){//result, method decl
			    ((int[])hmArgs.get(s))[25]++;//Rm
			} else if (valueSpec.compareTo("Nf")==0){//invariant, class field
			    ((int[])hmArgs.get(s))[26]++;//Rf
			} else if (valueSpec.compareTo("Np")==0){//parameter
			    ((int[])hmArgs.get(s))[27]++;//Rp
			}
		    }
		}//if containkeys
	    }//while next()
	
	    int[] sum=new int[30] ;
	    for (int i=0; i<strArgs.length;i++) {
		String s = strArgs[i];
		int[] eachSum = new int[30];
		/*non_null*/ int[] hmArgs_s=(int[]) hmArgs.get(s);
		eachSum[0] =hmArgs_s[0] ;//model method,Mm
		eachSum[1] =hmArgs_s[1] ;//method decl,Rm
		eachSum[2] =hmArgs_s[2] ;//mm
		eachSum[3] =hmArgs_s[3] ;//rm
		eachSum[4] =hmArgs_s[4] ;//Gf
		eachSum[5] =hmArgs_s[5] ;//Mf
		eachSum[6] =hmArgs_s[6] ;//Rf
		eachSum[7] =hmArgs_s[7] ;//gf
		eachSum[8] =hmArgs_s[8] ;//mf
		eachSum[9] =hmArgs_s[9] ;//rf
		eachSum[10] =hmArgs_s[10] ;//Mp
		eachSum[11] =hmArgs_s[11] ;//Rp
		eachSum[12] =hmArgs_s[12] ;//mp
		eachSum[13] =hmArgs_s[13] ;//rp
		//from spec
		//no overlap
		eachSum[14] =hmArgs_s[14] ;//Mm
		eachSum[15] =hmArgs_s[15] ;//Mf
		eachSum[16] =hmArgs_s[16] ;//Mp
		eachSum[17] =hmArgs_s[17] ;//Gf
		eachSum[18] =hmArgs_s[18] ;//Rm
		eachSum[19] =hmArgs_s[19] ;//Rf
		eachSum[20] =hmArgs_s[20] ;//Rp
		//overlap
		eachSum[21] =hmArgs_s[21] ;//Mm
		eachSum[22] =hmArgs_s[22] ;//Mf
		eachSum[23] =hmArgs_s[23] ;//Mp
		eachSum[24] =hmArgs_s[24] ;//Gf
		eachSum[25] =hmArgs_s[25] ;//Rm
		eachSum[26] =hmArgs_s[26] ;//Rf
		eachSum[27] =hmArgs_s[27] ;//Rp
		
		sum[0] += eachSum[0];
		sum[1] += eachSum[1];
		sum[2] += eachSum[2];
		sum[3] += eachSum[3];
		sum[4] += eachSum[4];
		sum[5] += eachSum[5];
		sum[6] += eachSum[6];
		sum[7] += eachSum[7];
		sum[8] += eachSum[8];
		sum[9] += eachSum[9];
		sum[10] += eachSum[10];
		sum[11] += eachSum[11];
		sum[12] += eachSum[12];
		sum[13] += eachSum[13];
		sum[14] += eachSum[14];
		sum[15] += eachSum[15];
		sum[16] += eachSum[16];
		sum[17] += eachSum[17];
		sum[18] += eachSum[18];
		sum[19] += eachSum[19];
		sum[20] += eachSum[20];
		sum[21] += eachSum[21];
		sum[22] += eachSum[22];
		sum[23] += eachSum[23];
		sum[24] += eachSum[24];
		sum[25] += eachSum[25];
		sum[26] += eachSum[26];
		sum[27] += eachSum[27];
		
		System.out.print(s+"\t"+eachSum[6]+"|");
		System.out.print(eachSum[19]+eachSum[26]+"|"+eachSum[26]+"|");
		System.out.print(eachSum[6]+eachSum[9]+"\t"); //normal field
		System.out.print(eachSum[5]+"|");
		System.out.print(eachSum[15]+eachSum[22]+"|"+eachSum[22]+"|");
		System.out.print(eachSum[5]+eachSum[8]+"\t");//model field
		System.out.print(eachSum[4]+"|");
		System.out.print(eachSum[17]+eachSum[24]+"|"+eachSum[24]+"|");
		System.out.print(eachSum[4]+eachSum[7]+"\t"); //ghost field
		System.out.print(eachSum[1]+"|");
		System.out.print(eachSum[18]+eachSum[25]+"|"+eachSum[25]+"|");
		System.out.print(eachSum[1]+eachSum[3]+"\t"); //normal method
		System.out.print(eachSum[0]+"|");
		System.out.print(eachSum[14]+eachSum[21]+"|"+eachSum[21]+"|");
		System.out.print(eachSum[0]+eachSum[2]+"\t"); //model method
		System.out.print(eachSum[11]+"|");
		System.out.print(eachSum[20]+eachSum[27]+"|"+eachSum[27]+"|");
		System.out.print(eachSum[11]+eachSum[13]+"\t");  //normal parameter
		System.out.print(eachSum[10]+"|");
		System.out.print(eachSum[16]+eachSum[23]+"|"+eachSum[23]+"|");
		System.out.println(eachSum[10]+eachSum[12]);//model parameter
	    }

	    System.out.print("Total:"+"\t"+sum[6]+"|");
	    System.out.print(sum[19]+sum[26]+"|"+sum[26]+"|");
	    System.out.print(sum[6]+sum[9]+"\t"); //normal field
	    System.out.print(sum[5]+"|");
	    System.out.print(sum[15]+sum[22]+"|"+sum[22]+"|");
	    System.out.print(sum[5]+sum[8]+"\t");//model field
	    System.out.print(sum[4]+"|");
	    System.out.print(sum[17]+sum[24]+"|"+sum[24]+"|");
	    System.out.print(sum[4]+sum[7]+"\t"); //ghost field
	    System.out.print(sum[1]+"|");
	    System.out.print(sum[18]+sum[25]+"|"+sum[25]+"|");
	    System.out.print(sum[1]+sum[3]+"\t"); //normal method
	    System.out.print(sum[0]+"|");
	    System.out.print(sum[14]+sum[21]+"|"+sum[21]+"|");
	    System.out.print(sum[0]+sum[2]+"\t"); //model method
	    System.out.print(sum[11]+"|");
	    System.out.print(sum[20]+sum[27]+"|"+sum[27]+"|");
	    System.out.print(sum[11]+sum[13]+"\t");  //normal parameter
	    System.out.print(sum[10]+"|");
	    System.out.print(sum[16]+sum[23]+"|"+sum[23]+"|");
	    System.out.println(sum[10]+sum[12]);//model parameter
    }

    public static void checkExpression(JExpression j,
				       JmlContext  context, 
				       String fn,
				       int clause, 
				       boolean ifNot, 
				       boolean ifInvStatic) 
	throws PositionedError 
    {
	if ( hmArgs.containsKey(fn)){
	    //try
	    if (j instanceof JmlEqualityExpression) {
		int oper = ((JmlEqualityExpression)j).oper();
		if (!( ifNot && oper== OPE_NE))// not !( != )
		    handleEqualityExpression ((JmlEqualityExpression)j,context,fn, clause,ifNot, ifInvStatic);
	    } else if (j instanceof JBitwiseExpression){
		if (((JBitwiseExpression)j).oper()==OPE_BAND){
		    checkExpression ( ((JBitwiseExpression)j).left(),context,fn,clause, ifNot , ifInvStatic);
		    checkExpression ( ((JBitwiseExpression)j).right(),context,fn,clause, ifNot , ifInvStatic);
		}
	    } else if (j instanceof JConditionalAndExpression){
		if ( ((JConditionalAndExpression)j).left() instanceof JBooleanLiteral){
		    JBooleanLiteral left = (JBooleanLiteral)((JConditionalAndExpression)j).left() ;
		
		    if (left.booleanValue()==false && !ifNot ){ //require xx && false, abort block
			j.check(context, clause!=2 ,JmlMessages.INVARIANT_FALSE );
			ifFalse = true;
			isLiteralFalse = true;
			if (!(clause ==3 && inExceptionalSpec)) // not ensures in expceptinal behavior
			    falseCount+=1;
			//System.out.println("left side is false");			
			return;
		    }
		}
		
		if ( ((JConditionalAndExpression)j).right() instanceof JBooleanLiteral){
		    JBooleanLiteral right = (JBooleanLiteral)((JConditionalAndExpression)j).right() ;
		     if (right.booleanValue()==false && !ifNot){//require xx && flase, abort block			
			 j.check(context, clause!=2 ,JmlMessages.INVARIANT_FALSE );
			 ifFalse = true;
			 isLiteralFalse = true;
			 if (!(clause ==3 && inExceptionalSpec))// not ensures in expceptinal behavior	
			     falseCount+=1;
			 return;
		     }
		}
		
		 //System.out.println( "in and expresion right is "+((JConditionalAndExpression)j).right().toString());
		checkExpression ( ((JConditionalAndExpression)j).left(),context,fn,clause,ifNot , ifInvStatic);
		checkExpression ( ((JConditionalAndExpression)j).right(), context,fn,clause, ifNot , ifInvStatic);
		
	    } else if (j instanceof JUnaryExpression) {
		if (((JUnaryExpression)j).oper()==OPE_LNOT) {
		    checkExpression ( ((JUnaryExpression)j).expr(),context,fn,clause,true, ifInvStatic);
		}
	    } else if (j instanceof JParenthesedExpression){
		checkExpression( ((JParenthesedExpression)j).expr(), context,fn,clause,ifNot, ifInvStatic);
	    } else if (j instanceof JmlFreshExpression){
		handleFreshExpression((JmlFreshExpression)j,context, clause,fn);
	    } else if (j instanceof JBooleanLiteral){
		// diverge true; no error report for ensure false
		if (((JBooleanLiteral)j).booleanValue()==true && clause ==5){
		    ifDiverges= true;
		}
		if (((JBooleanLiteral)j).booleanValue()==false && !ifNot) { 		
		    j.check(context, clause!=2 ,JmlMessages.INVARIANT_FALSE );

		    ifFalse = true;
		    isLiteralFalse = true;
		    if (!(clause ==3 && inExceptionalSpec))// not ensures in expceptinal behavior
			falseCount+=1;
		    return;
		}
	     } else if (j instanceof JInstanceofExpression ){
		 handleInstanceofExpression ((JInstanceofExpression) j, context,fn, clause, ifInvStatic);
	     } else if (j instanceof JmlNonNullElementsExpression ){
		 handleNNElementExpr((JmlNonNullElementsExpression)j, context, fn, clause, ifInvStatic);
	     }
	}
    }
    //check method specification

    //check specification;
    public static void checkSpecification(JmlMethodDeclaration jmd, Object[] jscArr, JmlContext context, String fn)
	throws PositionedError{	
	if ( hmArgs.containsKey(fn)){
	    intSpecCase =0;
	    ifFalse = false;
	    falseCount =0 ;
	    intConstructor =0;
	    isLiteralFalse = false;
	    inExceptionalSpec = false;
	    ifDiverges= false;
	    for (int i =jscArr.length-1; i>=0; i--)  {
		if (jscArr[i]==null)
		    intSpecCase+=1;
		else if (jscArr[i] instanceof JmlSpecCase)
		    checkSpecCase((JmlSpecCase)jscArr[i], context,fn, false);
		else if (jscArr[i] instanceof HashMap){
		    intSpecCase+=1;
		    HashMap hmTemp = (HashMap)jscArr[i];
		    Iterator it =hmTemp.keySet().iterator();
		    while (it.hasNext()){
			String key = (String)it.next();
			String s =key.substring(0,key.indexOf("|"));
			String value = (String)hmTemp.get(key);
			char c = value.charAt(1);
			if (s.compareTo(fn)==0){//if just one spec case in current method and it is require false
			    if (c=='m'){//method, equal to \result !=null
				//System.out.println("super class with explicit non_null as implicit with hmap");
				hmNnStat.put(key,"Nm");
				putHmSpecCase(key);
			    }else if (c=='p'){//parameter, equal to id !=null
				hmNnStat.put(key,"Np");
				putHmSpecCase(key);
			    }				
			}
		    }

		}
	    }
	    //System.out.println("there are " +jscArr.length+ " in method spec");
	}

	jmd.check(context, !(falseCount == jscArr.length && !ifDiverges) ,JmlMessages.METHOD_SPEC_INCONSISTENT);	

	Iterator it =hmSpecCase.keySet().iterator();
	while (it.hasNext()){
	    String key = (String)it.next();
	    String s =key.substring(0,key.indexOf("|"));
	    String strMethod = fn+"|"+currClass+"|"+currMethod;
	    if (s.compareTo(fn)==0){
		int value = Integer.parseInt((String)hmSpecCase.get(key));
		//System.out.println("in check specification , key is "+ key + "  value is "+(String)hmSpecCase.get(key) + " intSpecCase is "+intSpecCase);
		if (value != intSpecCase && key.indexOf(strMethod)!=-1)    hmNnStat.remove(key);
	    }
	}
    }

    public static void checkSpecCase( JmlSpecCase jsc, JmlContext context, String fn, boolean fromHeavy)  throws PositionedError {
	if (!(jsc instanceof JmlAbruptSpecCase) && !(jsc instanceof JmlModelProgram )){
	    if (!fromHeavy) intSpecCase+=1;
	    //if (!fromHeavy) System.out.println("in checkSPecCase "+intSpecCase);
	    if (jsc instanceof JmlGeneralSpecCase) {
		JmlGeneralSpecCase jg = (JmlGeneralSpecCase) jsc;
		if (jg.hasSpecHeader()){
		    JmlRequiresClause[] jrc = jg.specHeader();
		    isLiteralFalse = false;
		    for (int i=0;i<jrc.length;i++){
			checkExpression(jrc[i].predOrNot().specExpression().expression(),context, fn, 1, false, false);
			if (isLiteralFalse) {   //abort this speccase, including intSpecCase --, remove key form hashmap
			    abortCurrentSpecCase(fn);
			    return;
			}
		    }
		}
		if (jg.hasSpecBody()){
		    JmlSpecBody jsb = jg.specBody();
		    checkSpecBody(jsb, context, fn);
		}
	    } else if ( jsc instanceof JmlHeavyweightSpec){
		//System.out.println("in jml heavyweithtspec "+ intSpecCase);
		checkSpecCase(((JmlHeavyweightSpec)jsc).specCase(),context, fn, true);
	    }
	}
    }

    public static void checkSpecBody( JmlSpecBody jsb, JmlContext context, String fn)  throws PositionedError {
	if ((jsb instanceof JmlGenericSpecBody)||(jsb instanceof JmlNormalSpecBody) ||(jsb instanceof JmlExceptionalSpecBody) ){
	    if (jsb instanceof JmlExceptionalSpecBody){
		inExceptionalSpec = true;
	    } else {
		inExceptionalSpec = false;
	    }
	    if (jsb.isSpecCases()){
		JmlGeneralSpecCase[] jgArr = jsb.specCases();
		stackSpecCase.push(String.valueOf(intSpecCase));
		stackValue.push(hmSpecCase);
		//System.out.println("put intSpecCase into stack "+intSpecCase);
		intSpecCase =0;
		hmSpecCase =  new HashMap(10);
		
		for (int i=0; i<jgArr.length;i++) checkSpecCase(jgArr[i], context, fn, false);
		
		HashMap hmTemp = new HashMap(hmSpecCase);
		
		Iterator it =hmTemp.keySet().iterator();
		while (it.hasNext()){
		    String key = (String)it.next();
		    String s =key.substring(0,key.indexOf("|"));
		    if (s.compareTo(fn)==0){
			int value = Integer.parseInt((String)hmSpecCase.get(key));
			//System.out.println("key is "+ key + "  value is "+(String)hmSpecCase.get(key) + " intSpecCase is "+intSpecCase);
			if (value != intSpecCase) {
			    hmNnStat.remove(key);
			    hmSpecCase.remove(key);
			    //System.out.println("remove "+key +" from hm");
			}
		    }
		}

		intSpecCase = Integer.parseInt((String)stackSpecCase.pop())+1; // got one more level

		hmTemp.clear();
		hmTemp.putAll(hmSpecCase);		
		hmSpecCase = (HashMap) stackValue.pop();
		//System.out.println("intspecCase is "+intSpecCase);
		it =hmTemp.keySet().iterator();
		while (it.hasNext()){
		    String key = (String)it.next();
		    String s =key.substring(0,key.indexOf("|"));
		    if (s.compareTo(fn)==0){
			if  (hmSpecCase.containsKey(key)){// before, it has been existed
			    hmSpecCase.put(key,String.valueOf(intSpecCase));
			}else{ // not existed in its upper level
			    hmSpecCase.put(key, hmTemp.get(key));
			}
			//System.out.println("replace "+key+" with value "+intSpecCase);
		    }		
		}

	    }else if (jsb.isSpecClauses()){
		JmlSpecBodyClause[]  jsbcArr = jsb.specClauses();
		isLiteralFalse = false;
		for (int i=0; i<jsbcArr.length;i++){
		    checkSpecBodyClause(jsbcArr[i],context,fn);
		}
		if (isLiteralFalse){
		    abortCurrentSpecCase(fn);
		    return;
		}
		if (jsb instanceof JmlExceptionalSpecBody) {// if exception_behavior, add nonexisted result !=null
		    String str= fn+"|"+currClass+"|"+currMethod;
		    putHmSpecCase(str);
		}
	    }
	}
    }

    //only requires and ensures are considered
    public static void checkSpecBodyClause( JmlSpecBodyClause jsbc, JmlContext context, String fn) throws PositionedError{
	if (jsbc instanceof JmlRequiresClause)
	    checkExpression( ((JmlRequiresClause) jsbc).predOrNot().specExpression().expression(), context, fn, 1, false ,false);
	if (jsbc instanceof JmlEnsuresClause) {
	    checkExpression( ((JmlEnsuresClause) jsbc).predOrNot().specExpression().expression(), context, fn, 3, false,false);
	}
	if (jsbc instanceof JmlSignalsClause){
	    checkExpression( ((JmlSignalsClause) jsbc).predOrNot().specExpression().expression(),context,fn,4,false, false);
	}
	if (jsbc instanceof JmlDivergesClause){
	    checkExpression( ((JmlDivergesClause) jsbc).predOrNot().specExpression().expression(),context,fn,5,false, false);
	}
    }

    private static void handleNNElementExpr(JmlNonNullElementsExpression j, JmlContext context, String fn, int clause, boolean ifInvStatic){
	String str="";

	if (j.specExpression().expression() instanceof JmlResultExpression){
	    str = "result";
	} else if ( j.specExpression().expression() instanceof JExpression){
	    str =((JNameExpression) j.specExpression().expression()).toString();
	}

	if (str.compareTo("")!=0 && (clause ==1 || clause ==2 || clause ==3)){ // show in invariant,requires, ensures
	    if (str.compareTo("result")==0){//resul
		str=fn+"|"+currClass+"|"+currMethod;
		hmNnStat.put(str,"Nm");
		putHmSpecCase(str);
	    } else if (clause ==2){ // invarian
		str=fn+"|"+context.getHostClass().ident()+"|"+str;
		if (!hmNonnull.containsKey(str)){ // didn't declare, put sf if it is in static invairan
		    if (ifInvStatic) hmNonnullPut(str,"sf");
		    else hmNonnullPut(str,"if");
		} else {
		    if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
			hmNnStat.put(str,"Nf");
		}
	    } else if (clause ==1){
		str=fn+"|"+currClass+"|"+currMethod+"|"+str;
		hmNnStat.put(str,"Np");
		putHmSpecCase(str);
	    }
	}	
    }

    private static void handleInstanceofExpression ( JInstanceofExpression j, JmlContext context,String fn, int clause,  boolean ifInvStatic){
	String str="";
	if (j.expr() instanceof JNameExpression){
	    str =((JNameExpression) j.expr()).getName();
	} else if ( j.expr() instanceof JmlResultExpression){
	    str = "result";
	}
	
	if (str.compareTo("")!=0 && (clause ==1 || clause ==2 || clause ==3)){ // show in invariant,requires, ensures
	    if (str.compareTo("result")==0){//resul
		str=fn+"|"+currClass+"|"+currMethod;
		hmNnStat.put(str,"Nm");
		putHmSpecCase(str);
	    } else if (clause ==2){ // invarian
		str=fn+"|"+context.getHostClass().ident()+"|"+str;
		if (!hmNonnull.containsKey(str)){ // didn't declare, put sf if it is in static invairan
		    if (ifInvStatic) hmNonnullPut(str,"sf");
		    else hmNonnullPut(str,"if");
		} else {
		    if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
			hmNnStat.put(str,"Nf");
		}
	    } else if (clause ==1){
		str=fn+"|"+currClass+"|"+currMethod+"|"+str;
		hmNnStat.put(str,"Np");
		putHmSpecCase(str);
	    }
	}

    }

    //clause 3-ensures, 2-invariant, 1-requires
    //ifNot -true when it is from !
    private static void handleEqualityExpression( JmlEqualityExpression je, JmlContext context, String fn, int clause, boolean ifNot, boolean ifInvStatic){

	JExpression left = ((JmlEqualityExpression)je).left();
	JExpression right = ((JmlEqualityExpression)je).right();

	String str ="";
	int oper = je.oper();
	if  (oper == OPE_NE){
	    if (left.isLiteral() && (left.getLiteral() instanceof JNullLiteral) && (right instanceof JNameExpression)){
		str= ((JNameExpression) right).getName();
	    }else if (right.isLiteral() && (right.getLiteral() instanceof JNullLiteral) && (left instanceof  JNameExpression)){
		str= ((JNameExpression) left).getName();
	    }else if (left.isLiteral() && (left.getLiteral() instanceof JNullLiteral) && (right instanceof JmlResultExpression)){
		str="result";
	    }else if (right.isLiteral() &&(right.getLiteral() instanceof JNullLiteral)&& (left instanceof  JmlResultExpression)){
		str="result";
	    }
	    //System.out.println(left.toString()+left.getType().getSignature()+" "+right.toString()+"  "+intSpecCase);	
	    int id=0; //indicate where !=null appears
	    if (str.compareTo("")!=0){
		if (str.compareTo("result")==0){ //result,put className.methodName
		    str=currClass+"|"+currMethod;
		    id=2;
		}else if (clause==2){
		    id=1;
		    str=context.getHostClass().ident()+"|"+str;
		}else if ( clause==1){
		    id=0;
		    str=currClass+"|"+currMethod+"|"+str;
		} else {
		    id = -1;
		}
		str=fn+"|"+str;
		//System.out.println(" str is "+str);
		if (id!=-1){		
		    if (left.isLiteral() &&  !right.isLiteral() && (left.getLiteral() instanceof JNullLiteral)){ // null!=
			if (id==2){//resul
			    hmNnStat.put(str,"Nm");
			    putHmSpecCase(str);
			}else if (id ==1){//invarian
			    if (!hmNonnull.containsKey(str)){ // didn't declare, put sf if it is in static invairan
				if (ifInvStatic) hmNonnullPut(str,"sf");
				else hmNonnullPut(str,"if");
			    } else {			
				//System.out.println("str is "+str+" value is " +(String)hmNonnull.get(str));
				if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
				    hmNnStat.put(str,"Nf");
			    }
			}else if (id==0){
			    hmNnStat.put(str,"Np");
			    putHmSpecCase(str);
			}
		    }
		
		    if (right.isLiteral() &&  !left.isLiteral() && (right.getLiteral() instanceof JNullLiteral)){ // !=null
			if (id==2){//resul
			    hmNnStat.put(str,"Nm");
			    putHmSpecCase(str);
			}else if (id ==1){//invarian
			    if (!hmNonnull.containsKey(str)){ // didn't declare, put sf if it is in static invairan
				if (ifInvStatic) hmNonnullPut(str,"sf");
				else hmNonnullPut(str,"if");
			    } else {			
				//System.out.println("str is "+str+" value is " +(String)hmNonnull.get(str));
				if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
				    hmNnStat.put(str,"Nf");
			    }
			}else if (id==0){
			    //System.out.println("put str "+str+" as implicit non_null, left is "+left.toString()+" right is "+right.toString());
			    hmNnStat.put(str,"Np");
			    putHmSpecCase(str);
			}
		    }
		}
	    }
	} else if (oper == OPE_EQ){//if oper   !=

	    if (((left.isLiteral() && (left.getLiteral() instanceof JNullLiteral)) || (left instanceof JThisExpression)) && (right instanceof JNameExpression)){
		str= ((JNameExpression) right).getName();
	    }else if ( ((right.isLiteral() && (right.getLiteral() instanceof JNullLiteral))||(right instanceof JThisExpression)) && (left instanceof  JNameExpression)){
		str= ((JNameExpression) left).getName();
	    }else if (((left.isLiteral() && (left.getLiteral() instanceof JNullLiteral))||(left instanceof JThisExpression)) && (right instanceof JmlResultExpression)){
		str="result";
	    }else if (((right.isLiteral() &&(right.getLiteral() instanceof JNullLiteral))||(right instanceof JThisExpression))&& (left instanceof  JmlResultExpression)){
		str="result";
	    }

	    int id=0; //indicate where ==null appears
	    if (str.compareTo("")!=0){
		if (str.compareTo("result")==0){ //result,put className.methodName
		    str=currClass+"|"+currMethod;
		    id=2;
		}else if ( clause==2){
		    id=1;
		    str=((JmlContext) context).getHostClass().ident()+"|"+str;
		}else if ( clause==1){
		    id=0;
		    str=currClass+"|"+currMethod+"|"+str;
		} else {
		    id = -1;
		}
		//System.out.println("id is "+id+" str is "+str+" "+(((JmlContext) context).getCMethod().ident()));
		str=fn+"|"+str;
		
		if (id!=-1){
		
		    if (left.isLiteral() &&  !right.isLiteral() && (left.getLiteral() instanceof JNullLiteral)){ // null!=
			if (ifNot){// in !(a!=null)
			    if (id==2){//resul
				hmNnStat.put(str,"Nm");
				putHmSpecCase(str);
			    }else if (id ==1){//invarian
			    if (!hmNonnull.containsKey(str) && clause ==2) // didn't declare, put sf if it is in static invairan
				if (ifInvStatic) hmNonnullPut(str,"sf");
				else hmNonnullPut(str,"if");
			    else if (clause ==2){			

				//System.out.println("str is "+str+" value is " +(String)hmNonnull.get(str));
				if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
				    hmNnStat.put(str,"Nf");
			    }

			    }else if (id==0){
				hmNnStat.put(str,"Np");
				putHmSpecCase(str);
			    }
			}else if (hmNnStat.containsKey(str)){
			    hmNnStat.remove(str);
			}
		    }
		    if (right.isLiteral() && !left.isLiteral() && (right.getLiteral() instanceof JNullLiteral)){ // !=null
			if (ifNot){// in !(a==null)
			    if (id==2){//resul
				hmNnStat.put(str,"Nm");
				putHmSpecCase(str);				
			    }else if (id ==1){//invarian
			    if (!hmNonnull.containsKey(str) && clause ==2) // didn't declare, put sf if it is in static invairan
				if (ifInvStatic) hmNonnullPut(str,"sf");
				else hmNonnullPut(str,"if");
			    else if (clause ==2){			

				//System.out.println("str is "+str+" value is " +(String)hmNonnull.get(str));
				if ((((String)hmNonnull.get(str)).charAt(1)=='s' &&  ifInvStatic)||((((String)hmNonnull.get(str)).charAt(1)!='s' && !ifInvStatic)))//static field "Ns" and is from static invariant or non-satic field in nonstatic inv
				    hmNnStat.put(str,"Nf");
			    }

			    }else if (id==0){
				hmNnStat.put(str,"Np");
				putHmSpecCase(str);
			    }
			}else if (hmNnStat.containsKey(str)){
			    hmNnStat.remove(str);
			}
		    }
		
		    if ( (left instanceof JThisExpression && !(right instanceof JThisExpression)) || (right instanceof JThisExpression && !(left instanceof JThisExpression))){ // ==this or this==
			if (id==2){//resul
			    hmNnStat.put(str,"Nm");
			    putHmSpecCase(str);
			}else if (id ==1){//invarian
			    hmNnStat.put(str,"Nf");
			}else if (id==0){
			    hmNnStat.put(str,"Np");
			    putHmSpecCase(str);
			}				
		    }
		}
	    }
	}//oper ==
	       	
    }

    private static void handleFreshExpression( JmlFreshExpression jf, JmlContext context, int clause, String fn){

	String str ="";
	for (int i = 0; i < jf.specExpressionList().length; i++)
	    if ((jf.specExpressionList())[i].expression() instanceof JmlResultExpression){//resul
		
		str=currClass+"|"+currMethod;
		str=fn+"|"+str;
		hmNnStat.put(str,"Nm");
		putHmSpecCase(str);
	    }
    }

    public static void handleMethodDeclaration(JmlMethodDeclaration jmd,
					       JMethodDeclaration delegee, 
					       String fileName, 
					       JmlContext context)
    {
	CClass cc = context.getHostClass();
	String className = cc.ident();
	String str=fileName+"|"+className+"|"+jmd.ident();

	// System.out.println("\thandleMDecl: "+str);
	if (className.equals(jmd.ident()) && hmNonnull.containsKey(str)) {
	    // constructor, can have duplicate method
	    ++intConstructor;
	    String strTemp = (String)hmNonnull.get(str);

	    hmNonnullPut(str+String.valueOf(intConstructor), strTemp);
	    if (hmSpecCase!=null && hmSpecCase.containsKey(str)) hmSpecCase.remove(str);

	    if (hmNnStat.containsKey(str)){// constructor, can have duplicate method
		String strTemp1 = (String)hmNnStat.get(str);
		hmNnStat.put(str+String.valueOf(intConstructor), strTemp1);
	    }
	}
	if (cc instanceof JmlSourceClass) {
	    if (jmd.isDeclaredNonNull()) {
		if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)){
		    hmNonnullPut(str,"Mm");//Model and Non null
		}else if (delegee.returnType().isReference()){
		    hmNonnullPut(str,"Rm"); //non null without model
		    //System.out.println("the method is declared in  "+fileName);
		}
	    } else if (jmd.hasFlag(((JmlSourceClass)cc).jmlAccess().modifiers(),ACC_NON_NULL_BY_DEFAULT) && !jmd.hasFlag(jmd.modifiers(),ACC_NULLABLE)){// take it as implicit non_null
		    hmNnStat.put(str,"Nm");//implicit Non null
		    if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)){
			hmNonnullPut(str,"mm");//Model and Non null
		    }else if (delegee.returnType().isReference()){
			hmNonnullPut(str,"rm"); //non null without model		
		    }
	    }else {
		if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)&& delegee.returnType().isReference()){
		    hmNonnullPut(str,"mm");//Model
		}else if (delegee.returnType().isReference()){
		    hmNonnullPut(str,"rm"); //reference var
		}
	    }
	}

	//handling prameters
	JFormalParameter[] jf = jmd.parameters();
	for (int i=0;i<jf.length;i++){
	    if (jf[i] instanceof JmlFormalParameter){
		str=fileName+"|"+className+"|"+jmd.ident()+"|"+((JmlFormalParameter)jf[i]).ident();

		if (className.compareTo(jmd.ident())==0 && hmNonnull.containsKey(str)){// constructor
		    //hmNonnull.remove(str);
		    String strTemp = (String)hmNonnull.get(str);
		    String strTemp1 = fileName+"|"+className+"|"+jmd.ident()+String.valueOf(intConstructor)+"|"+((JmlFormalParameter)jf[i]).ident();
		    hmNonnullPut(strTemp1, strTemp);
		    if (hmSpecCase!=null && hmSpecCase.containsKey(str)) hmSpecCase.remove(str);

		    if (hmNnStat.containsKey(str)){// constructor, can have duplicate param
			//hmNnStat.remove(str);
			String strTemp2 = (String)hmNnStat.get(str);
			String strTemp3 = fileName+"|"+className+"|"+jmd.ident()+String.valueOf(intConstructor)+"|"+((JmlFormalParameter)jf[i]).ident();
			hmNnStat.put(strTemp3, strTemp2);
		    }
		}

		if (cc instanceof JmlSourceClass){
		    if (jf[i].isDeclaredNonNull() ) { 
			if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)){
			    hmNonnullPut(str,"Mp");
			}else if(((JmlFormalParameter)jf[i]).getType().isReference()) {
			    hmNonnullPut(str,"Rp");
			}
		    }else if (jmd.hasFlag(((JmlSourceClass)cc).jmlAccess().modifiers(),ACC_NON_NULL_BY_DEFAULT) && !jmd.hasFlag(((JmlFormalParameter)jf[i]).modifiers(),ACC_NULLABLE)){// take it as implicit non_null
			hmNnStat.put(str,"Np");//implicit Non null
			if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)){
			    hmNonnullPut(str,"mp");
			}else if(((JmlFormalParameter)jf[i]).getType().isReference()) {
			    hmNonnullPut(str,"rp");
			}
		    }else {
			if (jmd.hasFlag( jmd.modifiers(),ACC_MODEL)&&((JmlFormalParameter)jf[i]).getType().isReference()){
			    hmNonnullPut(str,"mp");//Model
			}else if (((JmlFormalParameter)jf[i]).getType().isReference()){
			    hmNonnullPut(str,"rp");
			}
		    }
		}
	    }
	}
    }

    public static void setCurrMethod(String methodIdent){
	currMethod = methodIdent;
    }

    public static void setCurrClass(String classIdent){
	currClass = classIdent;
    }

    public static boolean getSuperMethod(JmlSourceMethod sm)
    {
	JmlMethodDeclaration jmd = (JmlMethodDeclaration)sm.getAST();
	boolean bExplicit = true;

	if (jmd.overriddenMethods() == null)
	    return true; // why is this true?

	CMethodSet cms=jmd.overriddenMethods();
	for (int i=0; i<cms.size();i++){
	    CMethod cm = cms.getMethod(i);
	    if(cm instanceof JmlSourceMethod) {
		// System.out.println("\tcm isa " + cm + " " + cm.getClass());
		bExplicit = bExplicit && cm.isDeclaredNonNull() // Utils.hasFlag(cm.modifiers(),ACC_NON_NULL) 
		    && getSuperMethod((JmlSourceMethod)cm);
	    }
	}
	return bExplicit;
    }

    public static boolean getSuperParam(JmlSourceMethod sm, int i) throws PositionedError {
	JmlMethodDeclaration jmd = (JmlMethodDeclaration)sm.getAST();
	if (jmd.overriddenMethods() == null)
	    return true; // why is this true?

	boolean bExplicit = true;
	CMethodSet cms=jmd.overriddenMethods();
	for (int n=0; n<cms.size();n++){
	    CMethod cm = cms.getMethod(n);				
	    if(cm instanceof JmlSourceMethod) {
		JmlSourceMethod jm =(JmlSourceMethod) cm;
		JmlMethodDeclaration jmdecl = (JmlMethodDeclaration) jm.getAST();
		if(jmdecl.overriddenMethods() == null)
		    continue;

		JFormalParameter[] jfm = jmdecl.parameters();
		if (jfm[i] instanceof JmlFormalParameter) {
		    bExplicit = bExplicit 
			&& ((JmlFormalParameter)jfm[i]).isDeclaredNonNull() 
			&& getSuperParam(jm, i); // ?!?
		}
	    }
	}
	return bExplicit;
    }

    public static  Vector getSuperSpec(JmlMethodDeclaration jmd, String key){
	Vector jsc = new Vector();
	//if (jmd.overriddenMethods()!=null){ //no super method
	    CMethodSet cms=jmd.overriddenMethods();
	    for (int i=0; i<cms.size();i++){
		CMethod cm = cms.getMethod(i);				
		if  (cm instanceof JmlSourceMethod){
		    JmlSourceMethod jm =(JmlSourceMethod) cm;
		    JmlMemberDeclaration jmem = jm.getAST();// check explicit non_null
		    if (jmem instanceof JmlMethodDeclaration) {			
			JmlMethodDeclaration jmdecl = (JmlMethodDeclaration) jmem;

			if (jmdecl.overriddenMethods()!=null && jmdecl.overriddenMethods().size()!=0){ // with super, add all super specs
			    jsc.addAll(getSuperSpec(jmdecl,key));
			}else{//no super metod, add current spec to vector			
			    if (jm.getSpecification() !=null){
				JmlSpecCase[] jscArr = jm.getSpecification().specCases();				
				//System.out.println("no super method, there is "+jscArr.length+" spec case");
				if ( jscArr!=null)
				    for (int k=0;k<jscArr.length;k++)
					jsc.add(jscArr[k]); 			    				
			    } else {//no specs, return null;				
				boolean ifNull = false;
				HashMap hmTempJsc = new HashMap(10);
				//System.out.println("no super method, and  no specs, put hashmap "+key);
				if (jmdecl.isDeclaredNonNull()) {
				    // jmdecl.hasFlag(jmdecl.modifiers(),ACC_NON_NULL)) {
				    //System.out.println("super is explcit method nonnull");
				    hmTempJsc.put(key,"Nm");
				    ifNull = true;
				}
				
				JFormalParameter[] jf = jmdecl.parameters();
				for (int t=0;t<jf.length; t++)
				    if ( jf[t] instanceof JmlFormalParameter)
					if (jf[t].isDeclaredNonNull()) { 
					    // /*((JmlFormalParameter)jf[t]).isNonNull()*/ false // Chalin - FIXME
					    hmTempJsc.put( key + "|"+(jf[t]).ident(),"Np");
					    ifNull =true;
					}
				//if no explicit specification, add explicit non_null info
				if (ifNull) {/*System.out.println("super is not null");*/jsc.add(hmTempJsc); }
				else {jsc.add(null);/*System.out.println("super is null");*/}
			    }
			}
		    }
		}
	    }
	    return jsc;
    }

    //put value into hashmap, value++
    private static void putHmSpecCase(String key){
	if (hmSpecCase.get(key) !=null) {
	    int value = Integer.parseInt((String)hmSpecCase.get(key));
	    hmSpecCase.put(key,String.valueOf(++value));
	    //System.out.println("put "+key+" with  "+value+" into hm");
	} else {
	    hmSpecCase.put(key,String.valueOf(1));
	    //System.out.println("put "+key+" with 1 into hm");
	}
    }

    private static void abortCurrentSpecCase(String fn){
	HashMap hmFalse = new HashMap(hmSpecCase);
	Iterator it =hmFalse.keySet().iterator();
	while (it.hasNext()){
	    String key = (String)it.next();
	    String s =key.substring(0,key.indexOf("|"));
	    if (s.compareTo(fn)==0){
		int value = Integer.parseInt((String)hmFalse.get(key));
		if (value == intSpecCase)   { hmSpecCase.remove(key); hmNnStat.remove(key);}
	    }
	}
	//System.out.println("abort current spec case, intspeccase "+intSpecCase);
	intSpecCase-=1;
    }

    //------------------------------------------------------------------------------
    // Control access to hmNonnull:

    public static void hmNonnullPut(String key, String value) {
	// System.err.println("\thmNonnull put " + value + "\t" + key);
	//if("rp".equals(value))
	//    throw new IllegalArgumentException();
	hmNonnull.put(key,value);
    }
    
    //------------------------------------------------------------------------------

    private static boolean ifDiverges;//if spec block contains diverge true;
    private static boolean isLiteralFalse;
    private static boolean inExceptionalSpec;
    private static int falseCount;
    private static int intConstructor; // constructor counter
    private static int intSpecCase; // speccase[] length, no exceptional speccase is included
    private static String currMethod;
    private static String currClass;

    private static Stack stackValue;
    private static Stack stackSpecCase;
    private static String[] strArgs;

    private static /*@non_null*/HashMap hmSpecCase=new HashMap(); // store count number for jml spec

    public static boolean ifFalse;
    public static /*@non_null*/HashMap hmNnStat=new HashMap(); //store in Jml Specs, var with !=null, to avoid count twice
    public static /*@non_null*/HashMap hmArgs=new HashMap();
    public static /*@non_null*/HashMap hmNonnull=new HashMap(); //store sum of Non_null appearance
    public static /*@non_null*/HashMap hmSuperSpec=new HashMap();
}
