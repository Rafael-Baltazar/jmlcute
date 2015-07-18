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
 * $Id: Main.java,v 1.0 2009/02/20 16:48:06 henriquerebelo Exp $
 * 
 * This file is based on the original $Id: TransPostExpression2.java,v 1.14 2007/07/19 10:51:37 f_rioux Exp $
 * by Frederic Rioux (based on Yoonsik Cheon's work)
 */

package org.jmlspecs.ajmlrac;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;
import org.jmlspecs.ajmlrac.qexpr.AbstractExpressionVisitor;
import org.jmlspecs.checker.JmlOldExpression;
import org.jmlspecs.checker.JmlPreExpression;
import org.jmlspecs.checker.JmlResultExpression;
import org.jmlspecs.checker.JmlSpecExpressionWrapper;
import org.jmlspecs.checker.JmlSpecQuantifiedExpression;
import org.multijava.mjc.CType;
import org.multijava.mjc.JExpression;
import org.multijava.mjc.JFieldDeclarationType;
import org.multijava.mjc.JLocalVariableExpression;
import org.multijava.mjc.JTypeDeclarationType;
import org.multijava.mjc.JVariableDefinition;

/**
 * A RAC visitor class to translate JML expressions into Java source code.
 * 
 * @see TransExpression2
 * 
 * @author Henrique Rebelo
 * @version $Revision: 1.0 $
 */
public/*@ non_null_by_default */ class TransPostExpression2 extends TransExpression2 {
	// ----------------------------------------------------------------------
	// CONSTRUCTORS
	// ----------------------------------------------------------------------

	/**
	 * Constructs a new instance and translates the given
	 * post-expression.
	 *
	 * @param resultVar variable to store the result
	 */
	public TransPostExpression2( 
			VarGenerator varGen,
			RacContext ctx,
			VarGenerator oldVarGen,
			boolean forStatic,
			JExpression pred,
			String resultVar,
			JTypeDeclarationType typeDecl,
			String errorType) {
		super(varGen, ctx, pred, resultVar, typeDecl, errorType);
		this.oldVarGen = oldVarGen;
		this.oldExprs = new ArrayList();
		// by henrique rebelo
		this.oldVarDecl = new ArrayList();

		this.forStatic = forStatic;
	}

	protected void handleExceptionalTranslation(PositionnedExpressionException e){
		quantifiers = new Stack();	//reset static quantifier stack
		super.handleExceptionalTranslation(e);
	}

	// ----------------------------------------------------------------------
	// ACCESSORS
	// ----------------------------------------------------------------------

	/** Returns a list of old expressions (as <code>RacNode</code>) that
	 * must be executed in the pre-state. The declaration of a local 
	 * variable to hold the result of the expression is stored in the
	 * <code>name</code> field of class <code>RacNode</code>. This method
	 * must be called after translation.
	 */
	public List oldExprs() {
		perform();
		return this.oldExprs;
	}

	public List oldVarDecl() {
		return this.oldVarDecl;
	}

	// ----------------------------------------------------------------------
	// TRANSLATION
	// ----------------------------------------------------------------------

	/**
	 * Translates a JML pre expression.
	 */
	public void visitJmlPreExpression(JmlPreExpression self) {
		transPreExpression(self);
	}

	/**
	 * Translates a JML old expression.
	 */
	public void visitJmlOldExpression(JmlOldExpression self) {
		transPreExpression(self);
	}

	public void transPreExpression( JmlSpecExpressionWrapper self ) {

		// does the pre expression have any quantified variables?
		if (hasQuantifiedVar(self)) {
			//throw(new NotImplementedExpressionException(self.getTokenReference(), "Quantified variables in JML pre-state expression"));
			oldExpressionInQuantifiers(self);
			return;
		} 

		// Translates the pre expression such that it is to be
		// evaluated in the pre-state and stores the result into a
		// special private field of type TN_JMLVALUE.

		JExpression expr = self.specExpression();
		CType type = expr.getApparentType();

		// translate the pre expr with a fresh pre-state variable
		String var = oldVarGen.freshVar();

		TransExpression2 tr = new TransExpression2(oldVarGen, context, expr, var, typeDecl, errorType);
		tr.isInner = true;
		tr.thisIs = thisIs; //"this" issue for anonymous class

		String oldVar = varGen.freshOldVar();
		String oldStmt = tr.stmtAsString();

		// There is always the possibility that the evaluation of the old expression
		// failed. If so, rethrow the PositionnedExpressionException.
		if(!tr.isProperlyEvaluated()){
			throw tr.reportedException;
		}

		// like in: \old(null)
		if("null".equals(oldStmt)){
			RETURN_RESULT("null");
			return;
		}

		//String resultStr = TN_JMLVALUE + ".ofObject(" + TransUtils.wrapValue(type, oldStmt)+ ")";
		String resultStr = oldStmt; // modification due to use of aspects... by Henrique Rebelo
		resultStr = resultStr.replace("this.", "object$rac.");
		resultStr = resultStr.replace(typeDecl.getCClass().getJavaName()+".object$rac.", "object$rac.");
		resultStr = resultStr.replace(typeDecl.ident()+".object$rac.", "object$rac.");
		Pattern p = Pattern.compile("[[\\_]*[\\w]*[\\_]*]+super.");
	    Matcher m = p.matcher(resultStr);
	    if(!m.find()){
	    	resultStr = resultStr.replace("super.", "("+"("+typeDecl.getCClass().getSuperClass().getJavaName()+")"+"object$rac).");
	    }
		resultStr = resultStr.replace("delegee_"+typeDecl.ident()+"().", "");
		resultStr = resultStr.replace("this", "object$rac");
		
		oldVarDecl.add(TransUtils.toString(type) + " " + oldVar + ";");
		oldExprs.add(oldVar + " = " + resultStr + ";");

		// piggy-back the name of new old variable in the name field
		// of the RAC node; the node will be evaluated by the precondition
		// check method.

		RETURN_RESULT(oldVar); // modification due to use of aspects... by Henrique Rebelo
	}

	/** Translates the given JML quantified expression. It is overridden
	 * here to keep track of the set of quantifiers that enclose the old 
	 * expression currently being translated.
	 *
	 * @see #visitJmlPreExpression(JmlPreExpression)
	 * @see #visitJmlOldExpression(JmlOldExpression)
	 */

	public void visitJmlSpecQuantifiedExpression( 
			JmlSpecQuantifiedExpression self )
	{	       
		//super.visitJmlSpecQuantifiedExpression(self);       
		TransPostExpression2 t = new TransPostExpression2(varGen, context, oldVarGen, forStatic, expression, resultVar, typeDecl, errorType);
		quantifiers.push(self);
		LOG(this.toString() + " QStack push " + quantifiers.size());
		translateSpecQuantifiedExpression(t, self);	
		oldExprs.addAll(t.oldExprs);
		oldVarDecl.addAll(t.oldVarDecl);
		quantifiers.pop();
		LOG(this.toString() + " QStack pop " + quantifiers.size());
	}

	/**
	 * Translates a JML result expression.
	 */
	public void visitJmlResultExpression( JmlResultExpression self ) {
		RETURN_RESULT(VN_RESULT);
	}

	// ----------------------------------------------------------------------
	// HELPER METHODS
	// ----------------------------------------------------------------------

	/** Does the given old or pre expression, <code>expr</code>, have any
	 * free quantified variables? */

	private boolean hasQuantifiedVar(JmlSpecExpressionWrapper expr) {
		return new QVarChecker().hasQVar(expr);
	}

	/**
	 * Translates a JML old expression, <code>self</code>, enclosed in
	 * quantifiers. The translation generates code that evaluates the
	 * old expression for each combination of bound variables of
	 * quantifiers and stores the result to a private cache. The original
	 * old expression is replaced with cache lookup code.
	 * 
	 * <pre><jml>
	 * requires !quantifiers.isEmpty();
	 * //assignable oldExprs;
	 * </jml></pre>
	 */
	private void oldExpressionInQuantifiers(JmlSpecExpressionWrapper self) {
		JExpression expr = self.specExpression();
		CType type = expr.getApparentType();
		String mapVar = varGen.freshOldVar(); // cache variable
		// statements for evaluating old expression, E, of type T.
		//  T v = T_init;
		//  v = [[E]]
		//  mapVar.put(key, v);
		String var = oldVarGen.freshVar();
		String key = buildKey();

		// coerce to type TN_JMLVALUE with appropriate guard against 
		// undefinedness.
//		RacNode stmt = new TransOldExpression(oldVarGen,context,expr,var,typeDecl).stmt();

		TransExpression2 tr = new TransExpression2(oldVarGen,context,expr,var,typeDecl, errorType);
		RacNode stmt = tr.stmt(false);
		if(!tr.isProperlyEvaluated()){
			throw tr.reportedException;
		}

//		stmt = RacParser.parseStatement(
//				//"try {\n" +
//					"  " + TransUtils.toString(type) + " " + var + " = " +
//					TransUtils.defaultValue(type) + ";\n" +
//					"$0\n" +
//					"  " + mapVar + ".put(" + key + ", " +TN_JMLVALUE+ ".ofObject(" +
//					TransUtils.wrapValue(type, var) + "));"/* +
//    			"}\n" +
//    			"catch (JMLNonExecutableException jml$e0) {\n" +
//    			"  " + mapVar + ".put(" + key + 
//    			", " +TN_JMLVALUE+ ".ofNonExecutable());\n" +
//    			"}" +
//    			"catch (java.lang.Exception jml$e0) {\n" +
//    			"  " + mapVar + ".put(" + key + 
//    			", " +TN_JMLVALUE+ ".ofUndefined());\n" +
//    			"}"*/, 
//    			stmt.incrIndent());

		// iteration of the statement over bound variables
//		try {
//			TransQuantifiedExpression trans = null;
//			// As the variable quantifiers is a stack, the translation
//			// should be done in the reverse order, i.e., from the
//			// inner to outer quantifiers. Thanks to Peter Chan for
//			// reporting this error.
//			for (int i = quantifiers.size() - 1; i >= 0; i--) {
//				trans = new TransQuantifiedExpression(varGen, context,
//						(JmlSpecQuantifiedExpression)quantifiers.get(i), 
//						null, this);
//				stmt = trans.generateLoop(stmt);
//			}
//		} catch (NonExecutableQuantifierException e) {
//			/*
//    		// contextual interpretation of non-executable expression
//    		if (context.enabled() && type.isBoolean()) {
//    			RETURN_RESULT(RacParser.parseStatement(
//    					"// from a non_executable, boolean, JML clause\n" +
//    					context.angelicValue(GET_ARGUMENT()) +  ";"));
//    		} else {
//    			nonExecutableExpression();
//    		}
//    		return;*/
//			throw(new NotImplementedExpressionException(self.getTokenReference(), "The old expression in this quantifier"));
//		}

		// piggyback cache declaration in the name field
//		stmt.setVarDecl(PreValueVars.createVar(forStatic, 
//				"JMLOldExpressionCache",
//				mapVar,
//		"new JMLOldExpressionCache()"));
//		oldExprs.add(stmt);
		List fieldsName = new ArrayList();
		HashMap fieldsMap = new HashMap();
		String [] fields = tr.stmtAsString().split(" ");
		
		if((tr.stmtAsString().contains("[") && tr.stmtAsString().contains("]"))){
			for (int i = 0; i < fields.length; i++) {
				if(fields[i].contains("this.") || fields[i].contains(typeDecl.getCClass().getJavaName()+".")){
					String fieldName = fields[i].replaceAll("\\[(.)+\\]", "").split(" ")[0].replace("(", "").replace(")", "");
					JFieldDeclarationType[] typeFields = typeDecl.fields();
					for (int l = 0; l < typeFields.length; l++) {
						JVariableDefinition varDef = typeFields[l].variable();
						if(("this."+varDef.ident()).equals(fieldName)){
							fieldsName.add(fieldName);
						}
					}
				}
			}
			for (Iterator iterator = fieldsName.iterator(); iterator.hasNext();) {
				String currentField = (String) iterator.next();
				fieldsMap.put(currentField.replace("this.", "").replace(typeDecl.getCClass().getJavaName()+".", ""), mapVar);
				currentField = currentField.replace("this.", "object$rac.");
				oldVarDecl.add(TransUtils.toString(type) + "[] " + mapVar + ";");
				oldExprs.add(mapVar + " = new " + type + "["+currentField+".length];\n"+"      "+
						"System.arraycopy("+currentField+", 0, "+mapVar+", 0, "+currentField+".length );");
				mapVar = varGen.freshOldVar();
			}
		}
		else{
			for (int i = 0; i < fields.length; i++) {
				if(fields[i].contains("this.") || fields[i].contains(typeDecl.getCClass().getJavaName()+".")){
					String fieldName = fields[i];
					if(fieldName.startsWith("(")){
//						fieldName = fieldName.replaceFirst("(", "");
						fieldName = StringUtils.replaceOnce(fieldName, "(", "");
					}
					if(fieldName.startsWith("this.")){
						fieldName = fieldName.replaceFirst("this.", "");
						fieldName = fieldName.replace(".", "_");
						fieldsName.add("this."+fieldName.split("_")[0]);
					}
					else if(fieldName.startsWith(typeDecl.getCClass().getJavaName()+".")){
						fieldName = fieldName.replaceFirst(typeDecl.getCClass().getJavaName()+".", "");
						fieldName = fieldName.replace(".", "_");
						fieldsName.add(typeDecl.getCClass().getJavaName()+"."+fieldName.split("_")[0]);
					}
				}
			}
			for (Iterator iterator = fieldsName.iterator(); iterator.hasNext();) {
				String currentField = (String) iterator.next();
				fieldsMap.put(currentField.replace("this.", "").replace(typeDecl.getCClass().getJavaName()+".", ""), mapVar);
				currentField = currentField.replace("this.", "object$rac.");
				oldVarDecl.add("java.util.Collection " + mapVar + ";");
				oldExprs.add(mapVar + " = new java.util.HashSet();\n" + "      "+
						mapVar+ ".addAll("+currentField+");");
				mapVar = varGen.freshOldVar();
			}
		}

		// replace the old expr with cache lookup code
//		RacNode result = RacParser.parseStatement(
//		"if (" + mapVar + ".containsKey(" + key + ")) {\n" +
//		"  " + GET_ARGUMENT() + " = " +
//		TransUtils.unwrapObject(type, 
//		"((" +TN_JMLVALUE+ ")" +mapVar+ ".get(" +key+ ")).value()") 
//		+ ";\n" +
//		"} else {\n" +
//		"  throw JMLChecker.ANGELIC_EXCEPTION;\n" +
//		"}");
//		String result = TransUtils.unwrapObject(type,"((" +TN_JMLVALUE+ ")" +mapVar+ ".get(" +key+ ")).value()");
		String result = tr.stmtAsString().replace("this.", "").replace(typeDecl.getCClass().getJavaName()+".", "");
		for (Iterator iterator = fieldsMap.keySet().iterator(); iterator.hasNext();) {
			String currentKey = (String) iterator.next();
			if(result.contains(currentKey)){
				result = result.replace(currentKey, (String)fieldsMap.get(currentKey));
			}
		}
        
		RETURN_RESULT(result);        
	}            

	/** Returns a key for retrieving the value of old expression currently
	 * being translated. We store the old expression values as a mapping
	 * from quantified (bound) variables to values, and the quantified
	 * variables beomes a key. For example, if the quantifiers are 
	 * <code>x1</code>, <code>x2</code>, ..., <code>xn</code>, the key
	 * is <code>new Object[] { x1, x2, ..., xn }</code>, where 
	 * <code>xi</code> is wrapped if necessary.
	 *
	 * <pre><jml>
	 * requires !quantifiers.isEmpty();
	 * ensures \result != null;
	 * </jml></pre>
	 */
	private String buildKey() {
		StringBuffer code = new StringBuffer();
		code.append("new java.lang.Object[] { " );
		boolean isFirst = true;
		for (Iterator i = quantifiers.iterator(); i.hasNext(); ) {
			JVariableDefinition[] vars = 
				((JmlSpecQuantifiedExpression)i.next()).quantifiedVarDecls();
			for (int j = 0; j < vars.length; j++) {
				if (isFirst) {
					isFirst = false;
				} else {
					code.append(", ");
				}
				code.append(TransUtils.wrapValue(vars[j].getType(), 
						vars[j].ident()));
			}            
		}
		code.append(" }");
		return code.toString();
	}


	// ----------------------------------------------------------------------
	// INNER CLASS
	// ----------------------------------------------------------------------

	/**
	 * A class to check whether an expression has any references to 
	 * quantified variables.
	 */

	private class QVarChecker extends AbstractExpressionVisitor {
		public QVarChecker() {}

		/** Returns <code>true</code> if the expression <code>expr</code>
		 * contains any references to quantified variables.
		 */

		public boolean hasQVar(JExpression expr) {
			hasQVar = false;
			this.qvars = new HashSet();
			for (Iterator i = quantifiers.iterator(); i.hasNext(); ) {
				JVariableDefinition[] vars = 
					((JmlSpecQuantifiedExpression)i.next()).quantifiedVarDecls();
				for (int j = 0; j < vars.length; j++) {
					qvars.add(vars[j].ident());
				}
			}
			expr.accept(this);
			return hasQVar;
		}
		public void visitLocalVariableExpression( 
				JLocalVariableExpression self ) {
			if (qvars.contains(self.ident())) 
				hasQVar = true;
		}
		private boolean hasQVar;
		private Set qvars;
	}

	// ----------------------------------------------------------------------
	// DATA MEMBERS
	// ----------------------------------------------------------------------

	/** Indicates whether this translation is for a static method
	 * declaration. */
	// TODO useful???
	private boolean forStatic;

	/** A list of <code>RacNode</code>'s representing old expressions that 
	 * must be executed in the pre-state. */
	private List oldExprs;

	private List oldVarDecl;


	/** Variable generator to be used in the translation of old expression. 
	 */
	private VarGenerator oldVarGen;

	/** The set of quantifiers that enclose the old expression currently
	 * being translated.
	 * 
	 * <pre><jml>
	 * private invariant (\forall Object o; quantifiers.contains(o);
	 *   o instanceof JmlSpecQuantifiedExpression);
	 * </jml></pre>
	 */
	private static Stack quantifiers = new Stack();
}
