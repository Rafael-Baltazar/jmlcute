/*
 * Copyright (C) 2008-2013 Universidade Federal de Pernambuco and 
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
 * $Id: QDoxUtil.java,v 1.0 2013/05/17 13:00:38 henriquerebelo Exp $
 */

package org.jmlspecs.util;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;
import org.jmlspecs.ajmlrac.Main;
import org.multijava.util.compiler.PositionedError;

import com.thoughtworks.qdox.JavaDocBuilder;
import com.thoughtworks.qdox.model.Annotation;
import com.thoughtworks.qdox.model.DocletTag;
import com.thoughtworks.qdox.model.JavaClass;
import com.thoughtworks.qdox.model.JavaField;
import com.thoughtworks.qdox.model.JavaMethod;
import com.thoughtworks.qdox.model.TypeVariable;


public class QDoxUtil {

	public static String getTypeErasureForTypeDeclsInFile(File file, 
			boolean isGenericSource) throws FileNotFoundException,  IOException, PositionedError {
		BufferedReader buffer = null;
		StringBuffer bufferedFile = null;
		String fileAsString = "";
		String line = "";

		bufferedFile = new StringBuffer("");
		buffer = new BufferedReader(new FileReader( file ));
		line = buffer.readLine();
		while (line != null) {
			bufferedFile.append(line);
			bufferedFile.append("\n");
			line = buffer.readLine();
		}
		buffer.close();
		fileAsString = bufferedFile.toString();
	
		AspectUtil.getInstance().addJavaFileAsString(fileAsString);
		JavaDocBuilder qDoxFile = new JavaDocBuilder();
		qDoxFile.addSource(new FileReader(file));
		
		// handling JavaDocTags in File
		List<DocletTag> javaMethsWithDocletTagsFile = QDoxUtil.getAllJavaDocTagsInFile(qDoxFile);
		if(javaMethsWithDocletTagsFile.size() > 0){
			buffer = new BufferedReader(new StringReader(fileAsString));
			StringBuffer fileAsStringJavaDocProcessed = new StringBuffer("");
			line = buffer.readLine();
			int fileLineNumber = 1;
			while (line != null) {
				// if any
				String jmlClause = QDoxUtil.getJavaDocTagAsJMLClause(javaMethsWithDocletTagsFile, fileLineNumber);
				fileAsStringJavaDocProcessed.append(line).append(jmlClause);
				fileAsStringJavaDocProcessed.append("\n");
				line = buffer.readLine();
				fileLineNumber++;
			}
			buffer.close();
			fileAsString = StringUtils.replaceOnce(fileAsString, fileAsString, fileAsStringJavaDocProcessed.toString());
		}
		
		// handling javadoc tags in Java types that should be shifted
		List<JavaClass> javaDeclTypeWithJavadocTags = QDoxUtil.getAllDeclaredJavaTypesWithJavaDocTagsInFile(qDoxFile);
		for (Iterator<JavaClass> iterator = javaDeclTypeWithJavadocTags.iterator(); iterator
				.hasNext();) {
			JavaClass javaTypeWithJavadoc = iterator.next();
			String jmlClausesToShift = QDoxUtil.getJavaDocTagAsJMLClauseForTypeToShift(QDoxUtil.getAllJavaDocTagsInAJavaTypedDecl(javaTypeWithJavadoc));
			if(jmlClausesToShift.equals("")){
				continue;
			}
			buffer = new BufferedReader(new StringReader(fileAsString));
			int lineStart = javaTypeWithJavadoc.getLineNumber();
			int fileLineNumber = 1;
			StringBuffer TypeDeclUtilOpenBrace = new StringBuffer("");
			line = buffer.readLine();
			fileLineNumber = 1;
			while (line != null) {
				if(fileLineNumber >= lineStart){
					if(line.contains("{")){
						int indexOpenBrace = line.indexOf('{');
						String lineTmp = line.substring(0, (indexOpenBrace+1));
						TypeDeclUtilOpenBrace.append(lineTmp);
						break;
					}
					else{
						TypeDeclUtilOpenBrace.append(line);
						TypeDeclUtilOpenBrace.append("\n");
					}
				}
				line = buffer.readLine();
				fileLineNumber++;
			}
			buffer.close();
			String TypeDeclUtilOpenBraceStr = TypeDeclUtilOpenBrace.toString().trim();
			// processing java field tags
			// placing them where the JML compiler can understand - [[[hemr]]]
			fileAsString = StringUtils.replaceOnce(fileAsString, TypeDeclUtilOpenBraceStr, TypeDeclUtilOpenBraceStr+jmlClausesToShift);
		}// end for
		
		// handling javadoc tags in Java fields that should be shifted
		List<JavaField> javaDeclFieldsWithJavadocTags = QDoxUtil.getAllDeclaredJavaFieldsWithJavaDocTagsInFile(qDoxFile);
		for (Iterator<JavaField> iterator = javaDeclFieldsWithJavadocTags.iterator(); iterator
				.hasNext();) {
			JavaField javaFieldWithJavadoc = iterator.next();
			String jmlClausesToShift = QDoxUtil.getJavaDocTagAsJMLClauseForFieldToShift(QDoxUtil.getAllJavaDocTagsInAJavaFieldDecl(javaFieldWithJavadoc));
			if(jmlClausesToShift.equals("")){
				continue;
			}
			buffer = new BufferedReader(new StringReader(fileAsString));
			int lineStart = javaFieldWithJavadoc.getLineNumber();
			int fileLineNumber = 1;
			StringBuffer fieldDecl = new StringBuffer("");
			line = buffer.readLine();
			fileLineNumber = 1;
			while (line != null) {
				if(fileLineNumber >= lineStart){
					if(line.contains(";")){
						int indexSemiColon = line.lastIndexOf(';');
						fieldDecl.append(line.substring(0, indexSemiColon+1));
						break;
					}
					else{
						fieldDecl.append(line);
						fieldDecl.append("\n");
					}
				}
				line = buffer.readLine();
				fileLineNumber++;
			}
			buffer.close();
			String fieldDeclStr = fieldDecl.toString().trim();
			// processing java field tags
			// placing them where the JML compiler can understand - [[[hemr]]]
			fileAsString = StringUtils.replaceOnce(fileAsString, fieldDeclStr, fieldDeclStr+jmlClausesToShift);
		}// end for
		
		// Generic Source or any Java 5+ features (hopefully :-)
		if(isGenericSource){
			String actualFileAsString = fileAsString;
			bufferedFile.delete(0, (bufferedFile.length()-1)); // reset for later use

			// handling enum types
			List<JavaClass> javaDeclEnumTypes = QDoxUtil.getAllDeclaredJavaEnumTypesInFile(qDoxFile);
			if(javaDeclEnumTypes.size() > 0){
				fileAsString = QDoxUtil.getFileEnumTypeErasureProcessingAsString(bufferedFile, actualFileAsString, javaDeclEnumTypes);
			}
			
			// collecting all methods that lexically occur within a file
			bufferedFile.delete(0, (bufferedFile.length()-1)); // reset for later use
			List<JavaMethod> javaDeclMeths = QDoxUtil.getAllDeclaredJavaMethodsInFile(qDoxFile);
			if(file.getCanonicalPath().endsWith(".jml")){
				actualFileAsString = QDoxUtil.handleConstructDeclInJMLFileMode(bufferedFile, actualFileAsString, javaDeclMeths);
			}
			List<com.github.antlrjavaparser.api.body.BodyDeclaration> members = QDoxUtil.getAllDeclaredJavaMethodsInFile(actualFileAsString);
			List<String> fileMeths = QDoxUtil.getAllJavaMethodDeclLexicallyInFile(bufferedFile, actualFileAsString, javaDeclMeths, members);
			
			if(fileMeths.size() != javaDeclMeths.size()){
				System.out.println("file = "+file.getCanonicalPath());
				System.out.println("processed ---> "+fileMeths.size());
				System.out.println("really contains = "+javaDeclMeths.size());
			}
			
//			for (Iterator<String> iterator = fileMeths.iterator(); iterator.hasNext();) {
//				String currentMeth = iterator.next();
//				System.out.println("matchedMeth = "+currentMeth);
//			}
			
			fileAsString = QDoxUtil.stripMethBodies(fileAsString, javaDeclMeths, fileMeths); // method bodies stripped... [[[hemr]]]
			
//			eliminating the pattern --> default {return null;};
			fileAsString = fileAsString.replaceAll("default(\\s)*\\{(\\s)*return [\\w;]+(\\s)*\\};", ";");

			// handling annotated Java fields
			List<JavaField> javaDeclAnnotatedFields = QDoxUtil.getAllDeclaredAnnotatedJavaFieldsInFile(qDoxFile);
			List<com.github.antlrjavaparser.api.body.FieldDeclaration> javaDeclAnnotatedFields2 = QDoxUtil.getAllDeclaredAnnotatedJavaFieldsInFile(actualFileAsString);
			for (int i = 0; i < javaDeclAnnotatedFields.size(); i++) {
				JavaField annotatedJavaField = javaDeclAnnotatedFields.get(i);
				com.github.antlrjavaparser.api.body.FieldDeclaration annotatedJavaField2 = javaDeclAnnotatedFields2.get(i);
				
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer annotationArea = new StringBuffer("");
				StringBuffer annotationAreaCommented = new StringBuffer("");
				int lineStart = annotatedJavaField2.getAnnotations().get(0).getBeginLine();
				int lineEnd = annotatedJavaField2.getAnnotations().get(annotatedJavaField2.getAnnotations().size() - 1).getEndLine();
				line = buffer.readLine();
				int fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber >= lineStart){
						if(fileLineNumber == lineEnd){
							annotationArea.append(line);
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line.replace("@", "#")+"*/");
							break;
						}
						else{
							annotationArea.append(line);
							annotationArea.append("\n");
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line.replace("@", "#")+"*/");
							annotationAreaCommented.append("\n");
						}
					}				
					line = buffer.readLine();
					fileLineNumber++;
				} // end while
				buffer.close();
				// pre field annotations if any
				StringBuffer fieldDeclAnnotations = new StringBuffer("");
				if(annotationArea.toString().contains("@SpecPublic")){
					fieldDeclAnnotations.append("spec_public ");
				}
				if(annotationArea.toString().contains("@SpecProtected")){
					fieldDeclAnnotations.append("spec_protected ");
				}
				if(annotationArea.toString().contains("@NonNull")){
					fieldDeclAnnotations.append("non_null ");
				}
				if(annotationArea.toString().contains("@Nullable")){
					fieldDeclAnnotations.append("nullable ");
				}
				if(annotationArea.toString().contains("@Model")){
					fieldDeclAnnotations.append("model ");
				}
				
				// processing java field annotations
				String annotationAreaCommentedStr = QDoxUtil.getFieldAnnotationAreaCommentedProcessedWithJML(
						annotatedJavaField, annotationAreaCommented.toString());

				// doing the replacement
				int newLineEnd = annotatedJavaField2.getEndLine();
				lineStart = lineEnd;
				lineEnd = newLineEnd;
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer fileAsStringReplacement = new StringBuffer("");
				line = buffer.readLine();
				fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber == (lineStart + 1)){
						// placing them where the JML compiler can understand - [[[hemr]]]
						fileAsStringReplacement.append("/*@  "+fieldDeclAnnotations.toString()+"@*/"+" "+line);
						fileAsStringReplacement.append("\n");
					}
					else if(fileLineNumber == (lineEnd)){ // getting the end of field line
						// placing them where the JML compiler can understand - [[[hemr]]]
						fileAsStringReplacement.append(line+annotationAreaCommentedStr);
						fileAsStringReplacement.append("\n");
					}
					else{
						fileAsStringReplacement.append(line);
						fileAsStringReplacement.append("\n");
					}
					line = buffer.readLine();
					fileLineNumber++;
				} // end while
				buffer.close();
				
				fileAsString = fileAsStringReplacement.toString();
				// updating the current field annotations in the file
				// removing field annotations
				fileAsString = StringUtils.replaceOnce(fileAsString, annotationArea.toString(), "");
			}// end for
			
			// handling annotated Java Methods
			List<String> javaDeclMethsAnnotationArea = new ArrayList<String>();
			List<JavaMethod> javaDeclAnnotatedMeths = QDoxUtil.getAllDeclaredAnnotatedJavaMethodsInFile(qDoxFile);
			List<com.github.antlrjavaparser.api.body.BodyDeclaration> javaDeclAnnotatedMeths2 = QDoxUtil.getAllDeclaredAnnotatedJavaMethodsInFile(actualFileAsString);
			for (int i = 0; i < javaDeclAnnotatedMeths.size(); i++) {
				JavaMethod annotatedJavaMethod = javaDeclAnnotatedMeths.get(i);
				com.github.antlrjavaparser.api.body.BodyDeclaration annotatedJavaMethod2 = javaDeclAnnotatedMeths2.get(i);
				
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer annotationArea = new StringBuffer("");
				StringBuffer annotationAreaCommented = new StringBuffer("");
				int lineStart = annotatedJavaMethod2.getAnnotations().get(0).getBeginLine();
				int lineEnd = annotatedJavaMethod2.getAnnotations().get(annotatedJavaMethod2.getAnnotations().size() - 1).getEndLine();
				line = buffer.readLine();
				int fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber >= lineStart){
						if(fileLineNumber == lineEnd){
							annotationArea.append(line);
							annotationArea.append("\n");
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line+"*/");
							annotationAreaCommented.append("\n");
							break;
						}
						else{
							annotationArea.append(line);
							annotationArea.append("\n");
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line+"*/");
							annotationAreaCommented.append("\n");
						}
					}
					line = buffer.readLine();
					fileLineNumber++;
				} // end while
				// processing java method annotations
				String annotationAreaCommentedStr = QDoxUtil.getMethodAnnotationAreaCommentedProcessedWithJML(
						annotatedJavaMethod, annotationAreaCommented);
				
				// updating the current meth annotations in the file
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer fileStartCurrentMeth = new StringBuffer("");
				
				lineStart = annotatedJavaMethod.getLineNumber();
				lineEnd = annotatedJavaMethod2.getEndLine();
				line = buffer.readLine();
				fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber >= lineStart){
						if(fileLineNumber == lineEnd){
							fileStartCurrentMeth.append(line);
							fileStartCurrentMeth.append("\n");
							break;
						}
						else{
							fileStartCurrentMeth.append(line);
							fileStartCurrentMeth.append("\n");
						}
						
					}
					line = buffer.readLine();
					fileLineNumber++;
				}
				String fileAsStringTmp = StringUtils.replaceOnce(fileStartCurrentMeth.toString(), annotationArea.toString(), annotationAreaCommentedStr.toString());
				fileAsString = StringUtils.replaceOnce(fileAsString, fileStartCurrentMeth.toString(), fileAsStringTmp);
				javaDeclMethsAnnotationArea.add(annotationAreaCommentedStr);
			}// end for
			
			// handling annotated Java Types
			List<JavaClass> javaDeclAnnotatedTypes = QDoxUtil.getAllDeclaredAnnotatedJavaTypesInFile(qDoxFile);
			List<com.github.antlrjavaparser.api.body.TypeDeclaration> javaDeclAnnotatedTypes2 = QDoxUtil.getAllDeclaredAnnotatedJavaTypesInFile(actualFileAsString);
			for (int i = 0; i < javaDeclAnnotatedTypes.size(); i++) {
				JavaClass annotatedJavaType = javaDeclAnnotatedTypes.get(i);
				com.github.antlrjavaparser.api.body.TypeDeclaration annotatedJavaType2 = javaDeclAnnotatedTypes2.get(i);
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer annotationArea = new StringBuffer("");
				StringBuffer annotationAreaCommented = new StringBuffer("");
				int lineStart = annotatedJavaType2.getAnnotations().get(0).getBeginLine();
				int lineEnd = annotatedJavaType2.getAnnotations().get(annotatedJavaType2.getAnnotations().size() - 1).getEndLine();
//				System.out.println("lineStart = "+lineStart);
//				System.out.println("lineEnd = "+lineEnd);
				line = buffer.readLine();
				int fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber >= lineStart){
						if(fileLineNumber == lineEnd){
							annotationArea.append(line);
							annotationArea.append("\n");
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line.replace("@", "#")+"*/");
							annotationAreaCommented.append("\n");
							break;
						}
						else{
							annotationArea.append(line);
							annotationArea.append("\n");
							annotationAreaCommented.append("/*"+fileLineNumber+"*/"+"/* "+line.replace("@", "#")+"*/");
							annotationAreaCommented.append("\n");
						}
					}
					line = buffer.readLine();
					fileLineNumber++;
				} // end while
				
				// selecting the entire type decl
				buffer = new BufferedReader(new StringReader(fileAsString));
				StringBuffer typeDecl = new StringBuffer("");
                int newEnd = annotatedJavaType2.getEndLine();
				lineStart = lineEnd + 1;
				lineEnd = newEnd;
//				System.out.println("lineStart<new> = "+lineStart);
//				System.out.println("lineEnd<new> = "+lineEnd);
				line = buffer.readLine();
				fileLineNumber = 1;
				while (line != null) {
					if(fileLineNumber >= lineStart){
						if(fileLineNumber == lineEnd){
							typeDecl.append(line);
							typeDecl.append("\n");
						}
						else{
							typeDecl.append(line);
							typeDecl.append("\n");
						}
					}
					line = buffer.readLine();
					fileLineNumber++;
				}
				
				String typeJMLAnno = "";
				if(annotationArea.toString().contains("@NonNullByDefault")){
					typeJMLAnno = "/*@ non_null_by_default @*/";
				}
				if(annotationArea.toString().contains("@NullableByDefault")){
					typeJMLAnno = "/*@ nullable_by_default @*/" + typeJMLAnno;		
				}
				if(annotationArea.toString().contains("@SpecPublic")){
					typeJMLAnno = "/*@ spec_public @*/" + typeJMLAnno;
				}
				if(annotationArea.toString().contains("@SpecProtected")){
					typeJMLAnno = "/*@ spec_protected @*/" + typeJMLAnno;		
				}
				
				// processing java type annotations
				String annotationAreaCommentedStr = QDoxUtil.getTypeAnnotationAreaCommentedProcessedWithJML(
						annotatedJavaType, annotationAreaCommented.toString());
				
				// placing them where the JML compiler can understand - [[[hemr]]]
				String typeDeclStr = StringUtils.replaceOnce(typeDecl.toString(), "{", "{"+annotationAreaCommentedStr);
				
				// updating the current type annotations in the file
				// removing type annotations
				fileAsString = StringUtils.replaceOnce(fileAsString, annotationArea.toString(), typeJMLAnno);
				fileAsString = StringUtils.replaceOnce(fileAsString, typeDecl.toString(), typeDeclStr);
			}// end for
			
//			// collecting all methods that lexically occur within a file
			bufferedFile.delete(0, (bufferedFile.length()-1)); // reset for later use
			javaDeclMeths = QDoxUtil.getAllDeclaredJavaMethodsInFile(qDoxFile);
			fileMeths = QDoxUtil.getAllJavaMethodDeclLexicallyInFile(bufferedFile, fileAsString, javaDeclMeths, members);
//            System.out.println("fileMeths = "+fileMeths.size());
//			for (Iterator<String> iterator = fileMeths.iterator(); iterator.hasNext();) {
//				String currentMeth = iterator.next();
//				System.out.println("matchedMeth = "+currentMeth);
//			}
			fileAsString = QDoxUtil.getFileMethDeclsProcessed(fileAsString, javaDeclMeths, fileMeths, file);
			
			// final issues about JML type annotations
			Pattern jmlAnnoPattern = Pattern.compile("@(\\s)*Pure(\\b)(\\s)*(\\((\\s)*\\))?");
			Matcher jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ pure @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			jmlAnnoMatcher.reset();
			jmlAnnoPattern = Pattern.compile("@(\\s)*Helper(\\b)(\\s)*(\\((\\s)*\\))?");
			jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ helper @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			jmlAnnoMatcher.reset();
			jmlAnnoPattern = Pattern.compile("@(\\s)*Nullable(\\b)(\\s)*(\\((\\s)*\\))?");
			jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ nullable @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			jmlAnnoMatcher.reset();
			jmlAnnoPattern = Pattern.compile("@(\\s)*NonNull(\\b)(\\s)*(\\((\\s)*\\))?");
			jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ non_null @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			jmlAnnoMatcher.reset();
			jmlAnnoPattern = Pattern.compile("@(\\s)*SpecPublic(\\b)(\\s)*(\\((\\s)*\\))?");
			jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ spec_public @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			jmlAnnoMatcher.reset();
			jmlAnnoPattern = Pattern.compile("@(\\s)*SpecProtected(\\b)(\\s)*(\\((\\s)*\\))?");
			jmlAnnoMatcher = jmlAnnoPattern.matcher(fileAsString);
			while(jmlAnnoMatcher.find()){
				int numberOfNewLines = QDoxUtil.getLineNumbersQtd(jmlAnnoMatcher.group());
				fileAsString = StringUtils.replaceOnce(fileAsString, jmlAnnoMatcher.group(), "/*@ spec_protected @*/"+QDoxUtil.getNewLinesCaracter(numberOfNewLines));
			}
			fileAsString = fileAsString.replaceAll("/\\*(\\s)*/\\*@", "/*@");
			fileAsString = fileAsString.replaceAll("@\\*/(\\s)*\\*/", "@*/");
			// final issues due to annotation types support
			fileAsString = fileAsString.replace("@interface", "interface");
//			fileAsString = fileAsString.replaceAll("\"[\\w\"\\s+\\{\\}\\(\\)\\.]*(\\b)default(\\b)[\\w\"\\s+\\{\\}\\(\\)\\.]*\"", "\"\""); // improve! [[[hemr]]] **
			
			Pattern defaultTextPattern = Pattern.compile("\"[\\w\"\\s+\\{\\}\\(\\)\\.]*(\\b)default(\\b)[\\@\\-\\w\"\\s+\\{\\}\\(\\)\\.]*\"");
			Matcher defaultTextMatcher = defaultTextPattern.matcher(fileAsString);
			while(defaultTextMatcher.find()){
				fileAsString = StringUtils.replaceOnce(fileAsString, defaultTextMatcher.group(), defaultTextMatcher.group().replace("default", ""));
			}
			
			// handling default stmt in annotation types
			fileAsString = fileAsString.replaceAll("(\\b)default(\\b)(\\s)*[\\@\\-\\w\"\\s+\\{\\}\\(\\)\\.]*(\\s)*;", ";");
			
			// handling static imports to support java 5 mode
			Pattern staticImportPattern = Pattern.compile("import static (.)*;");
			Matcher staticImportMatcher = staticImportPattern.matcher(fileAsString);
			while(staticImportMatcher.find()){
				String staticImport = staticImportMatcher.group();
				staticImport = staticImport.substring(0, staticImport.lastIndexOf(".")).replace("static ", "")+";";
				fileAsString = StringUtils.replaceOnce(fileAsString, staticImportMatcher.group(), staticImport);
			}
			
			// handling standard Java 5 annotations
			if(fileAsString.contains("@Inherited")){
				fileAsString = fileAsString.replaceAll("@Inherited((\\s)*\\((\\s)*\\))?", "");
			}
			
			if(fileAsString.contains("@Override")){
				fileAsString = fileAsString.replaceAll("@Override((\\s)*\\((\\s)*\\))?", "");
			}
			
			if(fileAsString.contains("@Deprecated")){
				fileAsString = fileAsString.replaceAll("@Deprecated((\\s)*\\((\\s)*\\))?", "");
			}
			
			if(fileAsString.contains("@SuppressWarnings")){
				fileAsString = fileAsString.replaceAll("@SuppressWarnings((\\s)*\\(\"(.)*\"\\))?", "");
				fileAsString = fileAsString.replaceAll("@SuppressWarnings((\\s)*\\((\\s)*\\))?", "");
			}
			
			// handling dot dot dot in Java 5
			if(fileAsString.contains("...")){
				fileAsString = fileAsString.replace("...", "[]");
			}
			
		} // final generic treatment
		
		// for debuggin purposes remove the following comment - [[[hemr]]]
//		System.err.println(fileAsString);
		return fileAsString;
	}
	
	private static String getJavaDocTagAsJMLClauseForTypeToShift(List<DocletTag> docletTagFieldsToShift){
		StringBuffer jmlClauses = new StringBuffer("");
		for (Iterator<DocletTag> iterator = docletTagFieldsToShift.iterator(); iterator.hasNext();) {
			DocletTag docletTag = iterator.next();
			String tagName = docletTag.getName();
			String tagValue = docletTag.getValue().replaceAll("\n", "").replaceAll("\r", "");
			if(tagName.equals("model_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("model_method_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("model_field_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("invariant_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("constraint_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("initially_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
			else if(tagName.equals("represents_definition")){
				String clause = "/*@ "+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
		}
		return jmlClauses.toString();
	}
	
	private static String getJavaDocTagAsJMLClauseForFieldToShift(List<DocletTag> docletTagFieldsToShift){
		StringBuffer jmlClauses = new StringBuffer("");
		for (Iterator<DocletTag> iterator = docletTagFieldsToShift.iterator(); iterator.hasNext();) {
			DocletTag docletTag = iterator.next();
			String tagName = docletTag.getName();
			String tagValue = docletTag.getValue().replaceAll("\n", "").replaceAll("\r", "");
			if(tagName.equals("in")){
				String clauseKind = "in";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				jmlClauses.append(clause);
			}
		}
		return jmlClauses.toString();
	}
	
	private static String getJavaDocTagAsJMLClause(List<DocletTag> docletTags, int fileLineNumber){
		DocletTag foundTag = null;
		String result = "";
		for (Iterator<DocletTag> iterator = docletTags.iterator(); iterator.hasNext();) {
			DocletTag docletTag = iterator.next();
			if(docletTag.getLineNumber() == fileLineNumber){
				foundTag = docletTag;
			}
		}
		if(foundTag != null){
//			*/   /*10*/  /*@@*/  /** sample 
			String tagName = foundTag.getName();
			String tagValue = foundTag.getValue().replaceAll("\n", "").replaceAll("\r", "");
			if(tagName.equals("nullable_by_default")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "nullable_by_default";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("non_null_by_default")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "non_null_by_default";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("spec_case_header")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clause = "/*@ "+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("helper")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "helper";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("pure")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "pure";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("also")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "also";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("spec_public")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "spec_public";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("spec_protected")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "spec_protected";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("non_null")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "non_null";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("nullable")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "nullable";
				String clause = "/*@ "+clauseKind+" "+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("requires")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "requires";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("ensures")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "ensures";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("assignable")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "assignable";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("signals")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "signals";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("signals_only")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "signals_only";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("callable")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "callable";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("accessible")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "accessible";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("duration")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "duration";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("captures")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "captures";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
			else if(tagName.equals("working_space")){
				String start = "*/";
				String end = "/**";
				String line = "/*"+foundTag.getLineNumber()+"*/";
				String clauseKind = "working_space";
				String clause = "/*@ "+clauseKind+" "+tagValue+"@*/";
				result = start+line+clause+end;
			}
		}
		return result;
	}
	
	private static String getFieldAnnotationAreaCommentedProcessedWithJML(
			JavaField annotatedJavaField, String annotationAreaCommentedStr) {
		//start
		for (int i = 0; i < annotatedJavaField.getAnnotations().length; i++) {
			Annotation currentAnnotation = annotatedJavaField.getAnnotations()[i];
			// handling single JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.In")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "in_redundantly" : "in") : "in");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			// handling composite JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.InDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "in_redundantly" : "in") : "in");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}
		}
		return annotationAreaCommentedStr;
	}

	private static String getTypeAnnotationAreaCommentedProcessedWithJML(
			JavaClass annotatedJavaType, String annotationAreaCommentedStr) {
		//start
		for (int i = 0; i < annotatedJavaType.getAnnotations().length; i++) {
			Annotation currentAnnotation = annotatedJavaType.getAnnotations()[i];
			// handling single JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Invariant")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = (currentAnnotation.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentAnnotation.getProperty("header").toString())+" ":"");
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "invariant_redundantly" : "invariant") : "invariant");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Constraint")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = (currentAnnotation.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentAnnotation.getProperty("header").toString())+" ":"");
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "constraint_redundantly" : "constraint") : "constraint");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Initially")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = (currentAnnotation.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentAnnotation.getProperty("header").toString())+" ":"");
					String clauseKind = "initially";
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Represents")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = (currentAnnotation.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentAnnotation.getProperty("header").toString())+" ":"");
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "represents_redundantly" : "represents") : "represents");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Model")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = "model ";
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.ModelMethod")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = "model ";
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.ModelField")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String header = "model ";
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+header+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			// handling composite JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.InvariantDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = (currentDef.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentDef.getProperty("header").toString())+" ":"");
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "invariant_redundantly" : "invariant") : "invariant");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.ConstraintDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = (currentDef.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentDef.getProperty("header").toString())+" ":"");
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "constraint_redundantly" : "constraint") : "constraint");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.InitiallyDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = (currentDef.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentDef.getProperty("header").toString())+" ":"");
							String clauseKind = "initially";
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.RepresentsDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = (currentDef.getNamedParameterMap().containsKey("header")? QDoxUtil.preparePred(currentDef.getProperty("header").toString())+" ":"");
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "represents_redundantly" : "represents") : "represents");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.ModelDefinitions")){
				if(currentAnnotation.getPropertyMap().containsKey("value")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = "model ";
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}	
				}
				if(currentAnnotation.getPropertyMap().containsKey("fields")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("fields").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = "model ";
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}	
				}
				if(currentAnnotation.getPropertyMap().containsKey("methods")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("methods").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String header = "model ";
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+header+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}	
				}
			}
		}
		// end
		return annotationAreaCommentedStr;
	}

	// helper methods

	private static List<JavaMethod> getAllDeclaredJavaMethodsInFile(JavaDocBuilder qDoxFile){
		List<JavaMethod> result = new ArrayList<JavaMethod>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			JavaMethod [] javaDeclMethods = currentJavaDeclType.getMethods();
			for (int j = 0; j < javaDeclMethods.length; j++) {
				JavaMethod currentJavaDeclMethod = javaDeclMethods[j];
				result.add(currentJavaDeclMethod);
			}
		}
		Comparator<JavaMethod> COMPARE_BY_LINE_NUMBER = new Comparator<JavaMethod>() {
			public int compare(JavaMethod one, JavaMethod other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<com.github.antlrjavaparser.api.body.BodyDeclaration> getAllDeclaredAnnotatedJavaMethodsInFile(String fileAsString) throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException{
		com.github.antlrjavaparser.api.CompilationUnit cu = com.github.antlrjavaparser.JavaParser.parse(new ByteArrayInputStream(fileAsString.getBytes("UTF-8")));
		List<com.github.antlrjavaparser.api.body.BodyDeclaration> result = new ArrayList<com.github.antlrjavaparser.api.body.BodyDeclaration>();
		
		for (Iterator iterator = cu.getTypes().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.TypeDeclaration type = (com.github.antlrjavaparser.api.body.TypeDeclaration) iterator.next();
			if(type.getMembers() != null){
				for (Iterator iterator2 = type.getMembers().iterator(); iterator2
						.hasNext();) {
					com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
					if(member instanceof com.github.antlrjavaparser.api.body.ConstructorDeclaration){
						if(member.getAnnotations().size() > 0){
							result.add(member);
						}
					}
					else if(member instanceof com.github.antlrjavaparser.api.body.MethodDeclaration){
						if(member.getAnnotations().size() > 0){
							result.add(member);
						}
					}
					else if(member instanceof com.github.antlrjavaparser.api.body.AnnotationMemberDeclaration){
						if(member.getAnnotations().size() > 0){
							result.add(member);
						}
					}
					else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
						QDoxUtil.getAllDeclaredAnnotatedJavaMethodsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
					}
					else {
						continue;
					}
				}
			}
		}	
		Comparator<com.github.antlrjavaparser.api.body.BodyDeclaration> COMPARE_BY_LINE_NUMBER = new Comparator<com.github.antlrjavaparser.api.body.BodyDeclaration>() {
			public int compare(com.github.antlrjavaparser.api.body.BodyDeclaration one, com.github.antlrjavaparser.api.body.BodyDeclaration other) {
				return Integer.valueOf(one.getBeginLine()).compareTo(other.getBeginLine());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<com.github.antlrjavaparser.api.body.BodyDeclaration> getAllDeclaredJavaMethodsInFile(String fileAsString) throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException{
		com.github.antlrjavaparser.api.CompilationUnit cu = com.github.antlrjavaparser.JavaParser.parse(new ByteArrayInputStream(fileAsString.getBytes("UTF-8")));
		List<com.github.antlrjavaparser.api.body.BodyDeclaration> result = new ArrayList<com.github.antlrjavaparser.api.body.BodyDeclaration>();
		
		for (Iterator iterator = cu.getTypes().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.TypeDeclaration type = (com.github.antlrjavaparser.api.body.TypeDeclaration) iterator.next();
			if(type.getMembers() != null){
				for (Iterator iterator2 = type.getMembers().iterator(); iterator2
						.hasNext();) {
					com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
					if(member instanceof com.github.antlrjavaparser.api.body.ConstructorDeclaration){
						result.add(member);
					}
					else if(member instanceof com.github.antlrjavaparser.api.body.MethodDeclaration){
						result.add(member);
					}
					else if(member instanceof com.github.antlrjavaparser.api.body.AnnotationMemberDeclaration){
						result.add(member);
					}
					else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
						QDoxUtil.getAllDeclaredJavaMethodsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
					}
					else {
						continue;
					}
				}
			}
		}	
		Comparator<com.github.antlrjavaparser.api.body.BodyDeclaration> COMPARE_BY_LINE_NUMBER = new Comparator<com.github.antlrjavaparser.api.body.BodyDeclaration>() {
			public int compare(com.github.antlrjavaparser.api.body.BodyDeclaration one, com.github.antlrjavaparser.api.body.BodyDeclaration other) {
				return Integer.valueOf(one.getBeginLine()).compareTo(other.getBeginLine());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static void getAllDeclaredAnnotatedJavaMethodsInFileHelper(com.github.antlrjavaparser.api.body.TypeDeclaration type, 
			List<com.github.antlrjavaparser.api.body.BodyDeclaration> result){
		if(type.getMembers() != null){
			for (Iterator iterator2 = type.getMembers().iterator(); iterator2
					.hasNext();) {
				com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
				if(member instanceof com.github.antlrjavaparser.api.body.ConstructorDeclaration){
					if(member.getAnnotations().size() > 0){
						result.add(member);
					}
				}
				else if(member instanceof com.github.antlrjavaparser.api.body.MethodDeclaration){
					if(member.getAnnotations().size() > 0){
						result.add(member);
					}
				}
				else if(member instanceof com.github.antlrjavaparser.api.body.AnnotationMemberDeclaration){
					if(member.getAnnotations().size() > 0){
						result.add(member);
					}
				}
				else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
					QDoxUtil.getAllDeclaredAnnotatedJavaMethodsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
				}
				else {
					continue;
				}
			}
		}
	}
	
	private static void getAllDeclaredJavaMethodsInFileHelper(com.github.antlrjavaparser.api.body.TypeDeclaration type, 
			List<com.github.antlrjavaparser.api.body.BodyDeclaration> result){
		if(type.getMembers() != null){
			for (Iterator iterator2 = type.getMembers().iterator(); iterator2
					.hasNext();) {
				com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
				if(member instanceof com.github.antlrjavaparser.api.body.ConstructorDeclaration){
					result.add(member);
				}
				else if(member instanceof com.github.antlrjavaparser.api.body.MethodDeclaration){
					result.add(member);
				}
				else if(member instanceof com.github.antlrjavaparser.api.body.AnnotationMemberDeclaration){
					result.add(member);
				}
				else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
					QDoxUtil.getAllDeclaredJavaMethodsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
				}
				else {
					continue;
				}
			}
		}
	}
	
	private static List<com.github.antlrjavaparser.api.body.TypeDeclaration> getAllDeclaredAnnotatedJavaTypesInFile(String fileAsString) throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException{
		List<com.github.antlrjavaparser.api.body.TypeDeclaration> result = new ArrayList<com.github.antlrjavaparser.api.body.TypeDeclaration>();
		com.github.antlrjavaparser.api.CompilationUnit cu = com.github.antlrjavaparser.JavaParser.parse(new ByteArrayInputStream(fileAsString.getBytes("UTF-8")));
		for (Iterator iterator = cu.getTypes().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.TypeDeclaration type = (com.github.antlrjavaparser.api.body.TypeDeclaration) iterator.next();
			if(type.getAnnotations() != null && type.getAnnotations().size() > 0){
				result.add(type);
			}
			QDoxUtil.getAllDeclaredAnnotatedJavaTypesInFileHelper(type, result);
		}	
		Comparator<com.github.antlrjavaparser.api.body.TypeDeclaration> COMPARE_BY_LINE_NUMBER = new Comparator<com.github.antlrjavaparser.api.body.TypeDeclaration>() {
			public int compare(com.github.antlrjavaparser.api.body.TypeDeclaration one, com.github.antlrjavaparser.api.body.TypeDeclaration other) {
				return Integer.valueOf(one.getBeginLine()).compareTo(other.getBeginLine());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static void getAllDeclaredAnnotatedJavaTypesInFileHelper(com.github.antlrjavaparser.api.body.TypeDeclaration type, 
			List<com.github.antlrjavaparser.api.body.TypeDeclaration> result){
		if(type.getMembers() != null){
			for (Iterator iterator2 = type.getMembers().iterator(); iterator2
					.hasNext();) {
				com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
				if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
					if(member.getAnnotations() != null && member.getAnnotations().size() > 0){
						result.add((com.github.antlrjavaparser.api.body.TypeDeclaration)member);
					}
					QDoxUtil.getAllDeclaredAnnotatedJavaTypesInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
				}
				else {
					continue;
				}
			}
		}
	}
	
	private static List<JavaClass> getAllDeclaredAnnotatedJavaTypesInFile(JavaDocBuilder qDoxFile){
		List<JavaClass> result = new ArrayList<JavaClass>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			if(currentJavaDeclType.getAnnotations().length > 0){
				result.add(currentJavaDeclType);
			}
		}
		Comparator<JavaClass> COMPARE_BY_LINE_NUMBER = new Comparator<JavaClass>() {
			public int compare(JavaClass one, JavaClass other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<JavaClass> getAllDeclaredJavaTypesWithJavaDocTagsInFile(JavaDocBuilder qDoxFile){
		List<JavaClass> result = new ArrayList<JavaClass>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			if(currentJavaDeclType.getTags().length > 0){
				result.add(currentJavaDeclType);
			}
		}
		Comparator<JavaClass> COMPARE_BY_LINE_NUMBER = new Comparator<JavaClass>() {
			public int compare(JavaClass one, JavaClass other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}

	private static List<JavaField> getAllDeclaredAnnotatedJavaFieldsInFile(JavaDocBuilder qDoxFile){
		List<JavaField> result = new ArrayList<JavaField>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			JavaField [] javaDeclFields = currentJavaDeclType.getFields();
			for (int j = 0; j < javaDeclFields.length; j++) {
				JavaField currentJavaDeclField = javaDeclFields[j];
				if(currentJavaDeclField.getAnnotations().length > 0){
					result.add(currentJavaDeclField);
				}
			}
		}
		Comparator<JavaField> COMPARE_BY_LINE_NUMBER = new Comparator<JavaField>() {
			public int compare(JavaField one, JavaField other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<com.github.antlrjavaparser.api.body.EnumDeclaration> getAllDeclaredJavaEnumConstantsInFile(String fileAsString) 
			throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException{
		com.github.antlrjavaparser.api.CompilationUnit cu = com.github.antlrjavaparser.JavaParser.parse(new ByteArrayInputStream(fileAsString.getBytes("UTF-8")));
		List<com.github.antlrjavaparser.api.body.EnumDeclaration> result = new ArrayList<com.github.antlrjavaparser.api.body.EnumDeclaration>();
		for (Iterator iterator = cu.getTypes().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.TypeDeclaration type = (com.github.antlrjavaparser.api.body.TypeDeclaration) iterator.next();
			if(type instanceof com.github.antlrjavaparser.api.body.EnumDeclaration){
				result.add((com.github.antlrjavaparser.api.body.EnumDeclaration)type);
			}
			if(type.getMembers() != null){
				for (Iterator iterator2 = type.getMembers().iterator(); iterator2
						.hasNext();) {
					com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
					if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
						QDoxUtil.getAllDeclaredJavaEnumConstantsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
					}
					else {
						continue;
					}
				}
			}
		}	
		Comparator<com.github.antlrjavaparser.api.body.EnumDeclaration> COMPARE_BY_LINE_NUMBER = new Comparator<com.github.antlrjavaparser.api.body.EnumDeclaration>() {
			public int compare(com.github.antlrjavaparser.api.body.EnumDeclaration one, com.github.antlrjavaparser.api.body.EnumDeclaration other) {
				return Integer.valueOf(one.getBeginLine()).compareTo(other.getBeginLine());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<com.github.antlrjavaparser.api.body.FieldDeclaration> getAllDeclaredAnnotatedJavaFieldsInFile(String fileAsString) 
			throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException{
		com.github.antlrjavaparser.api.CompilationUnit cu = com.github.antlrjavaparser.JavaParser.parse(new ByteArrayInputStream(fileAsString.getBytes("UTF-8")));
		List<com.github.antlrjavaparser.api.body.FieldDeclaration> result = new ArrayList<com.github.antlrjavaparser.api.body.FieldDeclaration>();
		for (Iterator iterator = cu.getTypes().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.TypeDeclaration type = (com.github.antlrjavaparser.api.body.TypeDeclaration) iterator.next();
			if(type.getMembers() != null){
				for (Iterator iterator2 = type.getMembers().iterator(); iterator2
						.hasNext();) {
					com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
					if(member instanceof com.github.antlrjavaparser.api.body.FieldDeclaration){
						if(((com.github.antlrjavaparser.api.body.FieldDeclaration)member).getAnnotations().size() > 0){
							result.add((com.github.antlrjavaparser.api.body.FieldDeclaration)member);
						}
					}
					else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
						QDoxUtil.getAllDeclaredAnnotatedJavaFieldsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
					}
					else {
						continue;
					}
				}
			}
		}	
		Comparator<com.github.antlrjavaparser.api.body.FieldDeclaration> COMPARE_BY_LINE_NUMBER = new Comparator<com.github.antlrjavaparser.api.body.FieldDeclaration>() {
			public int compare(com.github.antlrjavaparser.api.body.FieldDeclaration one, com.github.antlrjavaparser.api.body.FieldDeclaration other) {
				return Integer.valueOf(one.getBeginLine()).compareTo(other.getBeginLine());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static void getAllDeclaredJavaEnumConstantsInFileHelper(com.github.antlrjavaparser.api.body.TypeDeclaration type, 
			List<com.github.antlrjavaparser.api.body.EnumDeclaration> result){
		if(type instanceof com.github.antlrjavaparser.api.body.EnumDeclaration){
			result.add((com.github.antlrjavaparser.api.body.EnumDeclaration)type);
		}
		if(type.getMembers() != null){
			for (Iterator iterator2 = type.getMembers().iterator(); iterator2
					.hasNext();) {
				com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
				 if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
					QDoxUtil.getAllDeclaredJavaEnumConstantsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
				}
				else {
					continue;
				}
			}
		}
	}
	
	private static void getAllDeclaredAnnotatedJavaFieldsInFileHelper(com.github.antlrjavaparser.api.body.TypeDeclaration type, 
			List<com.github.antlrjavaparser.api.body.FieldDeclaration> result){
		if(type.getMembers() != null){
			for (Iterator iterator2 = type.getMembers().iterator(); iterator2
					.hasNext();) {
				com.github.antlrjavaparser.api.body.BodyDeclaration member = (com.github.antlrjavaparser.api.body.BodyDeclaration) iterator2.next();
				if(member instanceof com.github.antlrjavaparser.api.body.FieldDeclaration){
					if(((com.github.antlrjavaparser.api.body.FieldDeclaration)member).getAnnotations().size() > 0){
						result.add((com.github.antlrjavaparser.api.body.FieldDeclaration)member);
					}
				}
				else if (member instanceof com.github.antlrjavaparser.api.body.TypeDeclaration){
					QDoxUtil.getAllDeclaredAnnotatedJavaFieldsInFileHelper((com.github.antlrjavaparser.api.body.TypeDeclaration)member, result);
				}
				else {
					continue;
				}
			}
		}
	}
	
	private static List<JavaField> getAllDeclaredJavaFieldsWithJavaDocTagsInFile(JavaDocBuilder qDoxFile){
		List<JavaField> result = new ArrayList<JavaField>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			JavaField [] javaDeclFields = currentJavaDeclType.getFields();
			for (int j = 0; j < javaDeclFields.length; j++) {
				JavaField currentJavaDeclField = javaDeclFields[j];
				if(currentJavaDeclField.getTags().length > 0){
					result.add(currentJavaDeclField);
				}
			}
		}
		Comparator<JavaField> COMPARE_BY_LINE_NUMBER = new Comparator<JavaField>() {
			public int compare(JavaField one, JavaField other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<JavaMethod> getAllDeclaredAnnotatedJavaMethodsInFile(JavaDocBuilder qDoxFile){
		List<JavaMethod> result = new ArrayList<JavaMethod>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			JavaMethod [] javaDeclMethods = currentJavaDeclType.getMethods();
			for (int j = 0; j < javaDeclMethods.length; j++) {
				JavaMethod currentJavaDeclMethod = javaDeclMethods[j];
				if(currentJavaDeclMethod.getAnnotations().length > 0){
					result.add(currentJavaDeclMethod);
				}
			}
		}
		Comparator<JavaMethod> COMPARE_BY_LINE_NUMBER = new Comparator<JavaMethod>() {
			public int compare(JavaMethod one, JavaMethod other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<DocletTag> getAllJavaDocTagsInAJavaTypedDecl(JavaClass type){
		List<DocletTag> result = new ArrayList<DocletTag>();
		if(type.getTags().length > 0){
			for (int i = 0; i < type.getTags().length; i++) {
				result.add(type.getTags()[i]);
			}
		}
		Comparator<DocletTag> COMPARE_BY_LINE_NUMBER = new Comparator<DocletTag>() {
			public int compare(DocletTag one, DocletTag other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<DocletTag> getAllJavaDocTagsInAJavaFieldDecl(JavaField field){
		List<DocletTag> result = new ArrayList<DocletTag>();
		if(field.getTags().length > 0){
			for (int i = 0; i < field.getTags().length; i++) {
				result.add(field.getTags()[i]);
			}
		}
		Comparator<DocletTag> COMPARE_BY_LINE_NUMBER = new Comparator<DocletTag>() {
			public int compare(DocletTag one, DocletTag other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}
	
	private static List<DocletTag> getAllJavaDocTagsInFile(JavaDocBuilder qDoxFile){
		List<DocletTag> result = new ArrayList<DocletTag>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			
			// type javadoc tags
			if(currentJavaDeclType.getTags().length > 0){
				for (int k = 0; k < currentJavaDeclType.getTags().length; k++) {
					result.add(currentJavaDeclType.getTags()[k]);
				}
			}
			// field javadoc tags
			JavaField [] javaDeclFields = currentJavaDeclType.getFields();
			for (int j = 0; j < javaDeclFields.length; j++) {
				JavaField currentJavaDeclField = javaDeclFields[j];
				if(currentJavaDeclField.getTags().length > 0){
					for (int k = 0; k < currentJavaDeclField.getTags().length; k++) {
						result.add(currentJavaDeclField.getTags()[k]);
					}
				}
			}
			// method javadoc tags
			JavaMethod [] javaDeclMethods = currentJavaDeclType.getMethods();
			for (int j = 0; j < javaDeclMethods.length; j++) {
				JavaMethod currentJavaDeclMethod = javaDeclMethods[j];
				if(currentJavaDeclMethod.getTags().length > 0){
					for (int k = 0; k < currentJavaDeclMethod.getTags().length; k++) {
						result.add(currentJavaDeclMethod.getTags()[k]);
					}
				}
			}
		}
		Comparator<DocletTag> COMPARE_BY_LINE_NUMBER = new Comparator<DocletTag>() {
			public int compare(DocletTag one, DocletTag other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}

	private static List<JavaField> getADeclaredJavaEnumerationFieldsInEnumType(JavaClass enumType){
		List<JavaField> result = new ArrayList<JavaField>();

		JavaField [] javaDeclFields = enumType.getFields();
		for (int j = 0; j < javaDeclFields.length; j++) {
			JavaField currentJavaDeclField = javaDeclFields[j];
			if(enumType.getLineNumber() == currentJavaDeclField.getLineNumber()){
				result.add(currentJavaDeclField);
			}
		}
		Comparator<JavaField> COMPARE_BY_LINE_NUMBER = new Comparator<JavaField>() {
			public int compare(JavaField one, JavaField other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}

	private static String getADeclaredJavaEnumerationFieldsInEnumTypeAsErasure(JavaClass enumType){
		List<JavaField> javaEnumFields = new ArrayList<JavaField>();
		StringBuffer code = new StringBuffer("");

		JavaField [] javaDeclFields = enumType.getFields();
		for (int j = 0; j < javaDeclFields.length; j++) {
			JavaField currentJavaDeclField = javaDeclFields[j];
			if(enumType.getLineNumber() == currentJavaDeclField.getLineNumber()){
				javaEnumFields.add(currentJavaDeclField);
			}
		}
		Comparator<JavaField> COMPARE_BY_LINE_NUMBER = new Comparator<JavaField>() {
			public int compare(JavaField one, JavaField other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(javaEnumFields, COMPARE_BY_LINE_NUMBER);

		for (Iterator<JavaField> iterator = javaEnumFields.iterator(); iterator.hasNext();) {
			JavaField javaEnumField = iterator.next();
			code.append("public /*@ nullable @*/static final "+javaEnumField.getType().getFullyQualifiedName()+" "+javaEnumField.getName()+" = null;");
		}

		return code.toString();
	}

	private static List<JavaClass> getAllDeclaredJavaEnumTypesInFile(JavaDocBuilder qDoxFile){
		List<JavaClass> result = new ArrayList<JavaClass>();
		JavaClass [] javaDeclTypes  = qDoxFile.getClasses();

		for (int i = 0; i < javaDeclTypes.length; i++) {
			JavaClass currentJavaDeclType = javaDeclTypes[i];
			if(currentJavaDeclType.isEnum()){
				result.add(currentJavaDeclType);
			}
		}
		Comparator<JavaClass> COMPARE_BY_LINE_NUMBER = new Comparator<JavaClass>() {
			public int compare(JavaClass one, JavaClass other) {
				return Integer.valueOf(one.getLineNumber()).compareTo(other.getLineNumber());
			}
		};
		Collections.sort(result, COMPARE_BY_LINE_NUMBER);
		return result;
	}

	private static HashMap<String, String> getGenericAndErasureTypeParametersForMethod(JavaClass clazz, JavaMethod meth){
		HashMap<String, String> result = new HashMap<String, String>();
		// adding the current type generic type parameters
		if(clazz.getTypeParameters().length > 0){
			TypeVariable [] typeVariables = clazz.getTypeParameters();
			for (int i = 0; i < typeVariables.length; i++) {
				TypeVariable currentTypeVariable = typeVariables[i];
				String genericType = currentTypeVariable.getName();
				String erasureType = currentTypeVariable.getValue();
				if(erasureType.equals("")){
					erasureType = "java.lang.Object";
				}
				result.put(genericType, erasureType);
			}
		}
		// adding the current method generic type parameters
		if(meth.getTypeParameters().length > 0){
			TypeVariable [] typeVariables = meth.getTypeParameters();
			for (int i = 0; i < typeVariables.length; i++) {
				TypeVariable currentTypeVariable = typeVariables[i];
				String genericType = currentTypeVariable.getName();
				String erasureType = currentTypeVariable.getValue();
				if(erasureType.equals("")){
					erasureType = "java.lang.Object";
				}
				result.put(genericType, erasureType);
			}
		}
		return result;
	}

	private static String stripMethBodies(
			String fileAsString, List<JavaMethod> javaDeclMeths,
			List<String> fileMeths) {
		int indexMeth = 0;
		for (Iterator<String> iterator = fileMeths.iterator(); iterator.hasNext();) {
			String returnTypeDefaultValue = "";
			String currentMeth = iterator.next();
			String currentMethStrippedBody = "";
			currentMethStrippedBody = currentMeth;
			JavaMethod javaMeth = javaDeclMeths.get(indexMeth);
			
			if(((javaMeth.getReturnType() != null) && !(javaMeth.isConstructor()))){
				if(!QDoxUtil.defaultValue(javaMeth.getReturnType().getFullyQualifiedName()).equals("")){
//					if(!isJMLFile){
						returnTypeDefaultValue = "return "+QDoxUtil.defaultValue(javaMeth.getReturnType().getFullyQualifiedName())+";";
//					}
				}
			}
			if(!currentMeth.equals("")){
				int openBraceIndex = currentMeth.indexOf('{');
				if(openBraceIndex != -1){
					String tmp = "";
					StringBuffer linesToAppend = new StringBuffer("");
					tmp = currentMeth.substring(openBraceIndex+1);
					int newLineCount = QDoxUtil.getLineNumbersQtd(tmp);
//					if(!isJMLFile){
						linesToAppend.append("{");
//					}
//					else{
//						linesToAppend.append(";");
//					}
					linesToAppend.append(QDoxUtil.getNewLinesCaracter(newLineCount));
					linesToAppend.append(returnTypeDefaultValue);
//					if(!isJMLFile){
						linesToAppend.append("}");
//					}
					//					currentMethStrippedBody = currentMeth.replaceAll("\\{[\\w\\W]*\\}", linesToAppend.toString());
					String body = currentMeth.substring(openBraceIndex, currentMeth.lastIndexOf("}")+1);
					currentMethStrippedBody = currentMeth.replace(body, linesToAppend.toString());
					fileAsString = StringUtils.replaceOnce(fileAsString, currentMeth, currentMethStrippedBody);
				}
			}
			indexMeth++;
		}
		return fileAsString;
	}
	
	private static String getFileMethDeclsProcessed(
			String fileAsString, List<JavaMethod> javaDeclMeths,
			List<String> fileMeths, File file) throws PositionedError {
		int indexMeth = 0;
		for (Iterator<String> iterator = fileMeths.iterator(); iterator.hasNext();) {
			String currentMethErasure = "";
			String currentMethErasureTmp = "";
			String currentMeth = iterator.next();
			JavaMethod javaMeth = javaDeclMeths.get(indexMeth);
			
			if(javaMeth.getAnnotations().length > 0){
				// processing method annotations including parameter ones
				String currentMethAnnoProcessed = QDoxUtil.removeNonJMLAnnotationParameters(currentMeth);
				fileAsString = StringUtils.replaceOnce(fileAsString, currentMeth, currentMethAnnoProcessed);
				currentMeth = currentMethAnnoProcessed;
			}
			currentMethErasureTmp = currentMeth;
			JavaClass onwerType = javaMeth.getParentClass();
			HashMap<String, String> genericAndErasureTypeParameters = QDoxUtil.getGenericAndErasureTypeParametersForMethod(onwerType, javaMeth);
			Set<String> genericTypes = genericAndErasureTypeParameters.keySet();

			for (Iterator<String> iterator2 = genericTypes.iterator(); iterator2
					.hasNext();) {
				String genericType = iterator2.next();
				String erasureType = genericAndErasureTypeParameters.get(genericType);
				currentMethErasureTmp = currentMethErasureTmp.replaceAll("(\\b)"+genericType+"(\\b)", erasureType);
				currentMethErasure = currentMethErasureTmp;
			}
			
			indexMeth++;
			if(!currentMethErasure.equals("")){
				// means that we have generic type parameters 
				if(currentMethErasure.contains("<") && currentMethErasure.contains(">")){
					int lp = currentMethErasure.lastIndexOf('(');
					String currentMethErasurePreArgs = currentMethErasure.substring(0, lp);
					String currentMethErasureArgs = currentMethErasure.substring(lp);
					String currentMethPreArgsWithoutDiamond = currentMethErasurePreArgs.replaceAll("\\<[\\w\\W]*\\>", "");
					String currentMethArgsWithoutDiamond = currentMethErasureArgs;
					currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replaceAll("\\<[\\w\\W]*\\>", "");
					while(currentMethArgsWithoutDiamond.contains("<")){
						int lD = currentMethArgsWithoutDiamond.indexOf("<");
						int rD = currentMethArgsWithoutDiamond.indexOf(">");
						if(lD > rD){
//							currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replaceFirst(">", "");
							currentMethArgsWithoutDiamond = StringUtils.replaceOnce(currentMethArgsWithoutDiamond, ">", "");
							lD = currentMethArgsWithoutDiamond.indexOf("<");
							rD = currentMethArgsWithoutDiamond.indexOf(">");
						}
						String diamond = currentMethArgsWithoutDiamond.substring(lD, (rD+1));
						currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replace(diamond, "");
					}

					if(currentMethArgsWithoutDiamond.contains(">")){
						currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replace(">", ""); // removing any residual from generics --- [[[hemr]]]
					}

					currentMethErasure = currentMethErasure.replace(currentMethErasurePreArgs, currentMethPreArgsWithoutDiamond).
							replace(currentMethErasureArgs, currentMethArgsWithoutDiamond);
				}

				fileAsString = StringUtils.replaceOnce(fileAsString, currentMeth, currentMethErasure);
				// handling crosscutting specs
				JavaClass ownerType = javaMeth.getParentClass();
				QDoxUtil.handlingCrosscutSpecs(file, javaMeth, currentMethErasure, ownerType);
			}
			else{
				// means that we have generic type parameters 
				if(currentMeth.contains("<") && currentMeth.contains(">")){
					String currentMethTmp = currentMeth;
					int lp = currentMeth.lastIndexOf('(');
					String currentMethPreArgs = currentMethTmp.substring(0, lp);
					String currentMethArgs = currentMethTmp.substring(lp);
					String currentMethPreArgsWithoutDiamond = currentMethPreArgs.replaceAll("\\<[\\w\\W]*\\>", "");
					String currentMethArgsWithoutDiamond = currentMethArgs;
					currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replaceAll("\\<[\\w\\W]*\\>", "");
					while(currentMethArgsWithoutDiamond.contains("<")){
						int lD = currentMethArgsWithoutDiamond.indexOf("<");
						int rD = currentMethArgsWithoutDiamond.indexOf(">");
						if(lD > rD){
//							currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replaceFirst(">", "");
							currentMethArgsWithoutDiamond = StringUtils.replaceOnce(currentMethArgsWithoutDiamond, ">", "");
							lD = currentMethArgsWithoutDiamond.indexOf("<");
							rD = currentMethArgsWithoutDiamond.indexOf(">");
						}
						String diamond = currentMethArgsWithoutDiamond.substring(lD, (rD+1));
						currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replace(diamond, "");
					}
					
					if(currentMethArgsWithoutDiamond.contains(">")){
						currentMethArgsWithoutDiamond = currentMethArgsWithoutDiamond.replace(">", ""); // removing any residual from generics --- [[[hemr]]]
					}
					
					currentMethTmp = currentMethTmp.replace(currentMethPreArgs, currentMethPreArgsWithoutDiamond).
							replace(currentMethArgs, currentMethArgsWithoutDiamond);
					fileAsString = StringUtils.replaceOnce(fileAsString, currentMeth, currentMethTmp);
					// handling crosscutting specs
					JavaClass ownerType = javaMeth.getParentClass();
					QDoxUtil.handlingCrosscutSpecs(file, javaMeth, currentMethTmp, ownerType);
				}
				else {
					// means that we have a method in a .jml file
					// handling crosscutting specs
					JavaClass ownerType = javaMeth.getParentClass();
					QDoxUtil.handlingCrosscutSpecs(file, javaMeth, currentMeth, ownerType);
				}
			}
		}
		return fileAsString;
	}

	private static void handlingCrosscutSpecs(File file, JavaMethod javaMeth,
			String currentMeth, JavaClass ownerType) throws PositionedError {
		boolean isAspect = false;
//		boolean isCrosscutSpec = false;
//		Annotation xciAnno = null;
		for (int i = 0; i < ownerType.getAnnotations().length; i++) {
			if(ownerType.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Aspect")){
				isAspect = true;
			}
//			if(ownerType.getAnnotations()[i].toString().startsWith("@org.jmlspecs.lang.annotation.AspectXCS")){
//				isCrosscutSpec = true;
//				xciAnno = ownerType.getAnnotations()[i];
//			}
		}
//		if(isAspect && isCrosscutSpec){
//			System.out.println("parsedMethTmp = "+currentMeth);
//			if(!ownerType.isInner()){
//				TokenReference tref = TokenReference.build(file, xciAnno.getLineNumber());
//				throw new PositionedError(tref, JmlMessages.INVALID_XCS_ANNOTATION_LOCATION, "");
//			}
//			// is to handle crosscut specs?
//			if(Main.aRacOptions.crosscuttingContractSpecifications()){
//				JavaDocBuilder qDoxJavaMethodParserForCrosscutSpecs = new JavaDocBuilder();
//				qDoxJavaMethodParserForCrosscutSpecs.addSource(new StringReader("public class JMethodParser{\n"+currentMeth+"\n}"));
//				JavaClass parsedClassTmp = qDoxJavaMethodParserForCrosscutSpecs.getClassByName("JMethodParser");
//				if(parsedClassTmp.getMethods().length == 1){
//					JavaMethod parsedMethTmp = parsedClassTmp.getMethods()[0];
//					parsedMethTmp.setAnnotations(javaMeth.getAnnotations());
//					parsedMethTmp.setParentClass(ownerType);
//					boolean isToInclude = false;
//					for (int i = 0; i < parsedMethTmp.getAnnotations().length; i++) {
//						if(parsedMethTmp.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation")){
//							isToInclude = true;
//						}
//					}
//					if(isToInclude){
//						AspectUtil.getInstance().appendCrosscutSpecMeth(parsedMethTmp);
//					}
//				}
//			}
//		}
		 if(isAspect){
			// means that we can have advice and pointcuts but is not a part of the crosscutting contract specification
			if(Main.aRacOptions != null){
				if(Main.aRacOptions.adviceChecking()){
					AspectUtil.getInstance().appendAspectDecl(ownerType);
					JavaDocBuilder qDoxJavaMethodParserForCrosscutSpecs = new JavaDocBuilder();
					qDoxJavaMethodParserForCrosscutSpecs.addSource(new StringReader("public class JMethodParser{\n"+currentMeth+"\n}"));
					// adding Java imports
					for (int i = 0; i < ownerType.getSource().getImports().length; i++) {
						qDoxJavaMethodParserForCrosscutSpecs.getSources()[0].addImport(ownerType.getSource().getImports()[i]);
					}
					JavaClass parsedClassTmp = qDoxJavaMethodParserForCrosscutSpecs.getClassByName("JMethodParser");
					if(parsedClassTmp.getMethods().length == 1){
						JavaMethod parsedMethTmp = parsedClassTmp.getMethods()[0];
						parsedMethTmp.setAnnotations(javaMeth.getAnnotations());
						parsedMethTmp.setParentClass(ownerType);
						// handling advice specs --- [[[hemr]
						boolean isToInclude = false;
						for (int i = 0; i < parsedMethTmp.getAnnotations().length; i++) {
							if(parsedMethTmp.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.A")){
								isToInclude = true;
							}
							if(parsedMethTmp.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Before")){
								isToInclude = true;
							}
						}
						if(isToInclude){
							AspectUtil.getInstance().appendAspectAdvice(parsedMethTmp);
						}
						// handling crosscutting contract specs for advice --- [[[hemr]
						isToInclude = false;
						boolean isPC = false;
						for (int i = 0; i < parsedMethTmp.getAnnotations().length; i++) {
							if(parsedMethTmp.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Pointcut")){
								isPC = true;
							}
						}
						isToInclude = isPC;
						if(isToInclude){
							AspectUtil.getInstance().appendCrosscutSpecMeth(parsedMethTmp);
						}
					}
				}
			}
		}
		else {
			// is to handle crosscut specs?
			if(Main.aRacOptions != null){
				if(Main.aRacOptions.crosscuttingContractSpecifications()){
					JavaDocBuilder qDoxJavaMethodParserForCrosscutSpecs = new JavaDocBuilder();
					try {
						qDoxJavaMethodParserForCrosscutSpecs.addSource(new StringReader("public class JMethodParser{\n"+currentMeth+"\n}"));
					} catch (java.lang.ArrayIndexOutOfBoundsException e) {
						// ignore for now...
					}
					catch (Exception e) {
//						System.out.println("owner = "+javaMeth.getParentClass().getName());
//						System.out.println("file = "+file.getAbsolutePath());
//						System.out.println("currentMeth = "+currentMeth);
						e.printStackTrace();
					}
					// adding Java imports
					for (int i = 0; i < ownerType.getSource().getImports().length; i++) {
						qDoxJavaMethodParserForCrosscutSpecs.getSources()[0].addImport(ownerType.getSource().getImports()[i]);
					}
					JavaClass parsedClassTmp = qDoxJavaMethodParserForCrosscutSpecs.getClassByName("JMethodParser");
					if(parsedClassTmp.getMethods().length == 1){
						JavaMethod parsedMethTmp = parsedClassTmp.getMethods()[0];
						parsedMethTmp.setAnnotations(javaMeth.getAnnotations());
						parsedMethTmp.setParentClass(ownerType);
						boolean isToInclude = false;
						boolean isPC = false;
						for (int i = 0; i < parsedMethTmp.getAnnotations().length; i++) {
							if(parsedMethTmp.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Pointcut")){
								isPC = true;
							}
						}
						isToInclude = isPC;
						if(isToInclude){
							AspectUtil.getInstance().appendCrosscutSpecMeth(parsedMethTmp);
						}
					}
				}
			}
		}
	}
	
	public static boolean iPCXCS(JavaMethod javaMeth){
		boolean isPCXCS = false;
		boolean isPC = false;
		for (int i = 0; i < javaMeth.getAnnotations().length; i++) {
			if((javaMeth.getAnnotations()[i].toString().startsWith("@org.aspectj.lang.annotation.Pointcut"))){
				isPC = true;
			}
		}
		isPCXCS = isPC;
		return isPCXCS;
	}
	
	private static boolean canAdd(String lineNumber, List<String> lineNumbers){
		boolean result = true;
		for (Iterator iterator = lineNumbers.iterator(); iterator.hasNext();) {
			String lineNumberTmp = (String) iterator.next();
			if(lineNumberTmp.equals(lineNumber)){
				result = false;
				break;
			}
			
		}
		return result;
	}
	
	private static List<String> getEnumConstantLineNumbersPerEnumDecl(com.github.antlrjavaparser.api.body.EnumDeclaration enumType){
		List<String> lineNumbers = new ArrayList<String>();
		for (Iterator iterator = enumType.getEntries().iterator(); iterator.hasNext();) {
			com.github.antlrjavaparser.api.body.EnumConstantDeclaration enumConstDecl = (com.github.antlrjavaparser.api.body.EnumConstantDeclaration) iterator.next();
			if(canAdd(enumConstDecl.getBeginLine()+"", lineNumbers)){
				lineNumbers.add(enumConstDecl.getBeginLine()+"");
			}
			if(canAdd(enumConstDecl.getEndLine()+"", lineNumbers)){
				lineNumbers.add(enumConstDecl.getEndLine()+"");
			}
		}
		return lineNumbers;
	}

	private static String getFileEnumTypeErasureProcessingAsString(
			StringBuffer bufferedFile, String fileAsString,
			List<JavaClass> javaDeclEnumTypes) throws IOException {
		BufferedReader buffer = null;
		String line = "";
		List<com.github.antlrjavaparser.api.body.EnumDeclaration> javaDeclEnumTypes2 = QDoxUtil.getAllDeclaredJavaEnumConstantsInFile(fileAsString);
		fileAsString = fileAsString.replace("enum ", "final class ");

		//		handling enumeration fields
		for (int i = 0; i < javaDeclEnumTypes.size(); i++) {
			JavaClass enumType = javaDeclEnumTypes.get(i);
			com.github.antlrjavaparser.api.body.EnumDeclaration enumType2 = javaDeclEnumTypes2.get(i);
			List<JavaField> enumTypeFields = QDoxUtil.getADeclaredJavaEnumerationFieldsInEnumType(enumType);
			if(enumTypeFields.size() > 0){
				String enumFieldsConverted = QDoxUtil.getADeclaredJavaEnumerationFieldsInEnumTypeAsErasure(enumType);
				List<String> listEnumConstLineNumbers = getEnumConstantLineNumbersPerEnumDecl(enumType2);
				buffer = new BufferedReader(new StringReader(fileAsString));
				bufferedFile.delete(0, (bufferedFile.length()-1)); // resetting buffer
				line = buffer.readLine();
				int lineStart = enumType2.getBeginLine();
				int lineEnd = enumType2.getEndLine();
				int lineNumber = 1;
				String lastLine = "";
				while (line != null) {
					if(listEnumConstLineNumbers.get(listEnumConstLineNumbers.size() - 1).equals(lineNumber+"")){
						lastLine = "/* "+line+" */#";
						fileAsString = StringUtils.replaceOnce(fileAsString, line, lastLine);
					}
					else if(listEnumConstLineNumbers.contains(lineNumber+"")){
						String lineProcessed = "/* "+line+" */";
						fileAsString = StringUtils.replaceOnce(fileAsString, line, lineProcessed);
					}
					line = buffer.readLine();
					lineNumber++;
				}
				buffer.close();
				fileAsString = StringUtils.replaceOnce(fileAsString, lastLine, lastLine.replace("#", enumFieldsConverted));
			}
		}
		
		return fileAsString;
	}
	
	private static String handleConstructDeclInJMLFileMode(StringBuffer bufferedFile, String fileAsString,
			List<JavaMethod> javaDeclMeths) throws IOException{
		
		BufferedReader buffer;
		String line;
		for (Iterator<JavaMethod> iterator = javaDeclMeths.iterator(); iterator
				.hasNext();) {
			JavaMethod javaMethod = iterator.next();
			if(!javaMethod.isConstructor()){
				continue;
			}
			int lineNumber = javaMethod.getLineNumber();
			buffer = new BufferedReader(new StringReader(fileAsString));
			line = buffer.readLine();
			int fileLineNumber = 1;
			boolean canStart = false;
			while (line != null) {
				if(lineNumber == fileLineNumber){ canStart = true;}
				if(canStart){
					bufferedFile.append(line);
					bufferedFile.append("\n");
					JavaDocBuilder qDoxJavaMethodParser = new JavaDocBuilder();
					try {
						qDoxJavaMethodParser.addSource(new StringReader("public class JMethodParser{\n"+bufferedFile.toString()+"\n}"));
						if(qDoxJavaMethodParser.getClassByName("JMethodParser").getMethods().length == 1){
							// if match the wanted contructor
							if(line.contains(";")){
								String lineProcessed = line.replace(";", "");
								fileAsString = StringUtils.replaceOnce(fileAsString, bufferedFile.toString(),bufferedFile.toString().replace(line, lineProcessed)+"{}");
							}
							bufferedFile.delete(0, (bufferedFile.length()-1));
							break;
						}
					} catch (com.thoughtworks.qdox.parser.ParseException e) {
						// continue if it is not a valid method or constructor... [[[hemr]]]
					}
				}
				line = buffer.readLine();
				fileLineNumber++;
			}
		}
		
		return fileAsString;
	}

//	private static List<String> getAllJavaMethodDeclLexicallyInFile(
//			StringBuffer bufferedFile, String fileAsString,
//			List<JavaMethod> javaDeclMeths, List<String> javaDeclMethsAnnotationArea) throws IOException {
//		List<String> fileMeths = new ArrayList<String>();
//		BufferedReader buffer;
//		String line;
//		for (Iterator<JavaMethod> iterator = javaDeclMeths.iterator(); iterator
//				.hasNext();) {
//			JavaMethod javaMethod = iterator.next();
//			int lineNumber = javaMethod.getLineNumber();
//			buffer = new BufferedReader(new StringReader(fileAsString));
//			line = buffer.readLine();
//			int fileLineNumber = 1;
//			boolean canStart = false;
//			while (line != null) {
//				if(lineNumber == fileLineNumber){ canStart = true;}
//				if(canStart){
//					bufferedFile.append(line);
//					bufferedFile.append("\n");
//					JavaDocBuilder qDoxJavaMethodParser = new JavaDocBuilder();
//					try {
//						qDoxJavaMethodParser.addSource(new StringReader("public class JMethodParser{\n"+bufferedFile.toString()+"\n}"));
//						if(qDoxJavaMethodParser.getClassByName("JMethodParser").getMethods().length == 1){
//							String methDecl = bufferedFile.toString();
//							methDecl = QDoxUtil.getMethDeclWithoutAnnotations(methDecl, javaDeclMethsAnnotationArea).trim();
//							fileMeths.add(methDecl);
//							bufferedFile.delete(0, (bufferedFile.length()-1));
//							break;
//						}
//					} catch (Exception e) {
//						// continue if it is not a valid method... [[[hemr]]]
//					}
//				}
//				line = buffer.readLine();
//				fileLineNumber++;
//			}
//		}
//		return fileMeths;
//	}
	
	private static List<String> getAllJavaMethodDeclLexicallyInFile(StringBuffer bufferedFile, String fileAsString,
			List<JavaMethod> javaDeclMeths, List<com.github.antlrjavaparser.api.body.BodyDeclaration> members) throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException {
		List<String> fileMeths = new ArrayList<String>();
		for (int i = 0; i < javaDeclMeths.size(); i++) {
			com.github.antlrjavaparser.api.body.BodyDeclaration member = members.get(i);
			int lineNumberStart = 0;
			int lineNumberEnd = 0;
			if(member.getAnnotations().size() > 0){
				if((member.getAnnotations().get(member.getAnnotations().size()-1).getEndLine() + 1) < member.getBeginLine()){
					lineNumberStart = member.getBeginLine();
				}
				else{
					lineNumberStart = member.getAnnotations().get(member.getAnnotations().size()-1).getEndLine() + 1;
				}
				if(member.getBeginComments() != null){
					lineNumberStart += member.getBeginComments().size();
				}
				lineNumberEnd = member.getEndLine();
			}
			else{
				lineNumberStart = member.getBeginLine();
				lineNumberEnd = member.getEndLine();
			}
			
//			System.out.println("javaMethod<name> = "+javaDeclMeths.get(i).getName());
//			System.out.println("javaMethod = "+javaDeclMeths.get(i).getLineNumber());
//			System.out.println("lineNumberStart = "+lineNumberStart); 
//			System.out.println("lineNumberEnd = "+lineNumberEnd); 
			
			BufferedReader buffer = null;
			String line = "";
			String meth = "";
			bufferedFile = new StringBuffer("");
			buffer = new BufferedReader(new StringReader(fileAsString));
			line = buffer.readLine();
			int fileLineNumber = 1;
			while (line != null) {
				if((fileLineNumber >= lineNumberStart) && (fileLineNumber <= lineNumberEnd)){
					bufferedFile.append(line);
					bufferedFile.append("\n");
				}
				line = buffer.readLine();
				fileLineNumber++;
			}
			buffer.close();
			meth = bufferedFile.toString();
			fileMeths.add(meth);
		}
		
		return fileMeths;
	}
	
//	private static List<String> getAllJavaMethodDeclLexicallyInFile(StringBuffer bufferedFile, String fileAsString,
//			List<JavaMethod> javaDeclMeths) throws com.github.antlrjavaparser.ParseException, UnsupportedEncodingException, IOException {
//		List<String> fileMeths = new ArrayList<String>();
//		List<com.github.antlrjavaparser.api.body.BodyDeclaration> members = QDoxUtil.getAllDeclaredJavaMethodsInFile(fileAsString);
//		for (int i = 0; i < javaDeclMeths.size(); i++) {
//			com.github.antlrjavaparser.api.body.BodyDeclaration member = members.get(i);
//			int lineNumberStart = 0;
//			int lineNumberEnd = 0;
//			if(member.getAnnotations().size() > 0){
//				if((member.getAnnotations().get(member.getAnnotations().size()-1).getEndLine() + 1) < member.getBeginLine()){
//					lineNumberStart = member.getBeginLine();
//				}
//				else{
//					lineNumberStart = member.getAnnotations().get(member.getAnnotations().size()-1).getEndLine() + 1;
//				}
//				if(member.getBeginComments() != null){
//					lineNumberStart += member.getBeginComments().size();
//				}
//				lineNumberEnd = member.getEndLine();
//			}
//			else{
//				lineNumberStart = member.getBeginLine();
//				lineNumberEnd = member.getEndLine();
//			}
//			
////			System.out.println("javaMethod<name> = "+javaDeclMeths.get(i).getName());
////			System.out.println("javaMethod = "+javaDeclMeths.get(i).getLineNumber());
////			System.out.println("lineNumberStart = "+lineNumberStart); 
////			System.out.println("lineNumberEnd = "+lineNumberEnd); 
//			
//			BufferedReader buffer = null;
//			String line = "";
//			String meth = "";
//			bufferedFile = new StringBuffer("");
//			buffer = new BufferedReader(new StringReader(fileAsString));
//			line = buffer.readLine();
//			int fileLineNumber = 1;
//			while (line != null) {
//				if((fileLineNumber >= lineNumberStart) && (fileLineNumber <= lineNumberEnd)){
//					bufferedFile.append(line);
//					bufferedFile.append("\n");
//				}
//				line = buffer.readLine();
//				fileLineNumber++;
//			}
//			buffer.close();
//			meth = bufferedFile.toString();
//			fileMeths.add(meth);
//		}
//		
//		return fileMeths;
//	}

	private static String getMethodAnnotationAreaCommentedProcessedWithJML(
			JavaMethod annotatedJavaMethod, StringBuffer annotationAreaCommented) {
		String annotationAreaCommentedStr = annotationAreaCommented.toString();
		Annotation[] methAnnotation = annotatedJavaMethod.getAnnotations();

		for (int i = 0; i < methAnnotation.length; i++) {
			Annotation currentAnnotation = methAnnotation[i];
			// handling single JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Requires")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "requires_redundantly" : "requires") : "requires");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Assignable")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "assignable_redundantly" : "assignable") : "assignable");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Ensures")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "ensures_redundantly" : "ensures") : "ensures");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Signals")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "signals_redundantly" : "signals") : "signals");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SignalsOnly")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "signals_only_redundantly" : "signals_only") : "signals_only");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Callable")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "callable_redundantly" : "callable") : "callable");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Accessible")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "accessible_redundantly" : "accessible") : "accessible");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Duration")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "duration_redundantly" : "duration") : "duration");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Captures")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "captures_redundantly" : "captures") : "captures");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.WorkingSpace")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					String clauseKind = (currentAnnotation.getNamedParameterMap().containsKey("redundantly")? 
							(currentAnnotation.getProperty("redundantly").toString().equals("true")? "working_space_redundantly" : "working_space") : "working_space");
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					String pred = QDoxUtil.preparePred(currentAnnotation.getProperty("value").toString());
					String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
			}

			// handling composite JML annotations
			if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.RequiresDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> requiresDefinitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = requiresDefinitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "requires_redundantly" : "requires") : "requires");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.AssignableDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "assignable_redundantly" : "assignable") : "assignable");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.EnsuresDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "ensures_redundantly" : "ensures") : "ensures");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SignalsDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "signals_redundantly" : "signals") : "signals");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SignalsOnlyDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "signals_only_redundantly" : "signals_only") : "signals_only");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.CallableDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "callable_redundantly" : "callable") : "callable");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.AccessibleDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "accessible_redundantly" : "accessible") : "accessible");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.DurationDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "duration_redundantly" : "duration") : "duration");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.CapturesDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "captures_redundantly" : "captures") : "captures");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.WorkingSpaceDefinitions")){
				@SuppressWarnings("unchecked")
				ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
				for (Iterator<Annotation> iterator2 = definitions
						.iterator(); iterator2.hasNext();) {
					Annotation currentDef =  iterator2.next();
					if(currentDef.getNamedParameterMap().containsKey("value")){
						String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
								(currentDef.getProperty("redundantly").toString().equals("true")? "working_space_redundantly" : "working_space") : "working_space");
						String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
						String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
						String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
						annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
					}
				}
			}
			// speccase
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SpecCase")){
				if(currentAnnotation.getNamedParameterMap().containsKey("header")){
					String header = QDoxUtil.preparePred((String)currentAnnotation.getProperty("header").getParameterValue());
					String clause = "/*@ "+header+" @*/";
					String preLineNumber = "/*"+currentAnnotation.getLineNumber()+"*/";
					annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("requiresDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("requiresDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "requires_redundantly" : "requires") : "requires");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("assignableDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("assignableDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "assignable_redundantly" : "assignable") : "assignable");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("ensuresDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("ensuresDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "ensures_redundantly" : "ensures") : "ensures");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("signalsDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("signalsDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "signals_redundantly" : "signals") : "signals");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("signalsOnlyDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("signalsOnlyDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "signals_only_redundantly" : "signals_only") : "signals_only");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("callableDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("callableDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "callable_redundantly" : "callable") : "callable");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("accessibleDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("accessibleDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "accessible_redundantly" : "accessible") : "accessible");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("durationDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("durationDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "duration_redundantly" : "duration") : "duration");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("capturesDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("capturesDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "captures_redundantly" : "captures") : "captures");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
				if(currentAnnotation.getNamedParameterMap().containsKey("workingSpaceDefinitions")){
					@SuppressWarnings("unchecked")
					ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("workingSpaceDefinitions").getParameterValue();
					for (Iterator<Annotation> iterator2 = definitions
							.iterator(); iterator2.hasNext();) {
						Annotation currentDef =  iterator2.next();
						if(currentDef.getNamedParameterMap().containsKey("value")){
							String clauseKind = (currentDef.getNamedParameterMap().containsKey("redundantly")? 
									(currentDef.getProperty("redundantly").toString().equals("true")? "working_space_redundantly" : "working_space") : "working_space");
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String pred = QDoxUtil.preparePred(currentDef.getProperty("value").toString());
							String clause = "/*@ "+clauseKind+" "+pred+"; @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
						}
					}
				}
			}//
			// also
			else if(currentAnnotation.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.Also")){
				if(currentAnnotation.getNamedParameterMap().containsKey("value")){
					if(currentAnnotation.getProperty("value").getParameterValue() instanceof ArrayList){
						@SuppressWarnings("unchecked")
						ArrayList<Annotation> definitions = (ArrayList<Annotation>)currentAnnotation.getProperty("value").getParameterValue();
						for (Iterator<Annotation> iterator2 = definitions
								.iterator(); iterator2.hasNext();) {
							Annotation currentDef =  iterator2.next();
							if(currentDef.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SpecCase")){
								String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
								String clause = "/*@ also @*/";
								annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
								
								if(currentDef.getNamedParameterMap().containsKey("header")){
									String header = QDoxUtil.preparePred((String)currentDef.getProperty("header").getParameterValue());
									clause = "/*@ "+header+" @*/";
									preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
									annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
								}

								if(currentDef.getNamedParameterMap().containsKey("requiresDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("requiresDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "requires_redundantly" : "requires") : "requires");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("assignableDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("assignableDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "assignable_redundantly" : "assignable") : "assignable");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("ensuresDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("ensuresDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "ensures_redundantly" : "ensures") : "ensures");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("signalsDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("signalsDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "signals_redundantly" : "signals") : "signals");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("signalsOnlyDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("signalsOnlyDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "signals_only_redundantly" : "signals_only") : "signals_only");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("callableDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("callableDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "callable_redundantly" : "callable") : "callable");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("accessibleDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("accessibleDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "accessible_redundantly" : "accessible") : "accessible");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("durationDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("durationDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "duration_redundantly" : "duration") : "duration");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("capturesDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("capturesDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "captures_redundantly" : "captures") : "captures");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}

								if(currentDef.getNamedParameterMap().containsKey("workingSpaceDefinitions")){
									@SuppressWarnings("unchecked")
									ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("workingSpaceDefinitions").getParameterValue();
									for (Iterator<Annotation> iterator3 = definitions2
											.iterator(); iterator3.hasNext();) {
										Annotation currentDef2 =  iterator3.next();
										if(currentDef2.getNamedParameterMap().containsKey("value")){
											String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
													(currentDef2.getProperty("redundantly").toString().equals("true")? "working_space_redundantly" : "working_space") : "working_space");
											String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
											String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
											String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
											annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
										}
									}
								}
							}
						}
					}
					else{
						Annotation currentDef = (Annotation)currentAnnotation.getProperty("value").getParameterValue();
						if(currentDef.getType().getFullyQualifiedName().equals("org.jmlspecs.lang.annotation.SpecCase")){
							String preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
							String clause = "/*@ also @*/";
							annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
							
							if(currentDef.getNamedParameterMap().containsKey("header")){
								String header = QDoxUtil.preparePred((String)currentDef.getProperty("header").getParameterValue());
								clause = "/*@ "+header+" @*/";
								preLineNumber = "/*"+currentDef.getLineNumber()+"*/";
								annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber, clause+preLineNumber);
							}

							if(currentDef.getNamedParameterMap().containsKey("requiresDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("requiresDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "requires_redundantly" : "requires") : "requires");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("assignableDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("assignableDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "assignable_redundantly" : "assignable") : "assignable");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("ensuresDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("ensuresDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "ensures_redundantly" : "ensures") : "ensures");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("signalsDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("signalsDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "signals_redundantly" : "signals") : "signals");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("signalsOnlyDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("signalsOnlyDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "signals_only_redundantly" : "signals_only") : "signals_only");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("callableDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("callableDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "callable_redundantly" : "callable") : "callable");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("accessibleDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("accessibleDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "accessible_redundantly" : "accessible") : "accessible");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("durationDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("durationDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "duration_redundantly" : "duration") : "duration");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("capturesDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("capturesDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "captures_redundantly" : "captures") : "captures");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}

							if(currentDef.getNamedParameterMap().containsKey("workingSpaceDefinitions")){
								@SuppressWarnings("unchecked")
								ArrayList<Annotation> definitions2 = (ArrayList<Annotation>)currentDef.getProperty("workingSpaceDefinitions").getParameterValue();
								for (Iterator<Annotation> iterator3 = definitions2
										.iterator(); iterator3.hasNext();) {
									Annotation currentDef2 =  iterator3.next();
									if(currentDef2.getNamedParameterMap().containsKey("value")){
										String clauseKind = (currentDef2.getNamedParameterMap().containsKey("redundantly")? 
												(currentDef2.getProperty("redundantly").toString().equals("true")? "working_space_redundantly" : "working_space") : "working_space");
										String preLineNumber2 = "/*"+currentDef2.getLineNumber()+"*/";
										String pred = QDoxUtil.preparePred(currentDef2.getProperty("value").toString());
										String clause2 = "/*@ "+clauseKind+" "+pred+"; @*/";
										annotationAreaCommentedStr = annotationAreaCommentedStr.replace(preLineNumber2, clause2+preLineNumber2);
									}
								}
							}
						}
					}
				}
			}
		}
		return annotationAreaCommentedStr;
	}
	
	private static String getMethDeclWithoutAnnotations(String methDecl, List<String> javaDeclMethsAnnotationArea){
		for (Iterator<String> iterator = javaDeclMethsAnnotationArea.iterator(); iterator
				.hasNext();) {
			String header = iterator.next();
			methDecl = methDecl.replace(header, "");
		}
		return methDecl;
	}
	
	private static boolean isJMLAnnotation(String annotation){
		boolean result = false;
		if(annotation.equals("@Model()") ||
			   annotation.equals("@Nullable()") ||
				annotation.equals("@NonNull()")||
				annotation.equals("@SpecPublic()")||
				annotation.equals("@SpecProtected()")||
				annotation.equals("@Pure()")){
			result = true;
		}
		return result;
	}
	
	private static boolean isParenBalanced(String token){
		boolean ret = false;
		Pattern lParenPattern = Pattern.compile("\\(");
		Matcher lParenMatcher = lParenPattern.matcher(token);
		int lParenLineCount = 0;
		while(lParenMatcher.find()){
			lParenLineCount++;
		}
		Pattern rParenPattern = Pattern.compile("\\)");
		Matcher rParenMatcher = rParenPattern.matcher(token);
		int rParenLineCount = 0;
		while(rParenMatcher.find()){
			rParenLineCount++;
		}

		if(lParenLineCount == rParenLineCount){
			ret = true;
		}
		return ret;
	}
	
	private static String removeNonJMLAnnotationParameters(String currentMethTmp) {
		String currentMethTmp2 = currentMethTmp;
		
		Pattern tmpPattern = Pattern.compile("/\\*(.|\\s)*@(.|\\s)*\\*/");
		Matcher tmpMatcher = tmpPattern.matcher(currentMethTmp2);
		while(tmpMatcher.find()){
			currentMethTmp2 = currentMethTmp2.replace(tmpMatcher.group(), "");
		}
		
		Pattern annoPattern = Pattern.compile("@(\\s)*(.)*(\\s)*(\\((.)*\\))");
		Matcher annoMatcher = annoPattern.matcher(currentMethTmp2);
		while(annoMatcher.find()){
			String group = annoMatcher.group();
			char [] groupAsChar = group.toCharArray();
			boolean canCheck = false;
			boolean foundAt = false;
			StringBuffer matchedAnnotation = new StringBuffer("");
			for (int i = 0; i < groupAsChar.length; i++) {
				if(groupAsChar[i] == '('){
					canCheck = true;
				}
				if(groupAsChar[i] == '@'){
					foundAt = true;
				}
				if(foundAt){
					matchedAnnotation.append(groupAsChar[i]);	
				}
				if(canCheck){
					if(QDoxUtil.isParenBalanced(matchedAnnotation.toString())){
						// if is not JML annotation, we remove it...
						if(!isJMLAnnotation(matchedAnnotation.toString())){
							currentMethTmp = StringUtils.replaceOnce(currentMethTmp, matchedAnnotation.toString(), "");	
						}
						matchedAnnotation = new StringBuffer("");
						canCheck = false;
						foundAt = false;
					}
				}
			}
		}
		return currentMethTmp;
	}
	
	private static int getLineNumbersQtd(String tmp) {
		int newLineCount = 0;
		
		BufferedReader buffer = new BufferedReader(new StringReader(tmp));
		String line = null;
		try {
			line = buffer.readLine();
			while (line != null) {
				line = buffer.readLine();
				newLineCount++;
			}
			buffer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return newLineCount-1;
	}
	
	private static String getNewLinesCaracter(int numberOfNewLines){
		StringBuffer result = null;
		result = new StringBuffer("");
		for (int i = 0; i < numberOfNewLines; i++) {
			result.append("\n");
		}
		return result.toString();
	}

	private static String preparePred(String clause){
		Pattern pattern = Pattern.compile("(\"[^\"]*\")*");
		Matcher patterhMatcher = pattern.matcher(clause);
		StringBuffer clauseParsed = new StringBuffer("");
		while(patterhMatcher.find()){
			clauseParsed.append(patterhMatcher.group());
		}
		return clauseParsed.toString().replace("\"", "").replace("#dq", "\"").replace("#sq", "\'").replace("#", "\\");
	}

	private static String defaultValue(String type) {
		String result = "";

		if(!type.equals("void")){
			if(type.equals("boolean")){
				result = "false";
			}
			else if(type.equals("byte")){
				result = "(byte) 0";
			}
			else if(type.equals("short")){
				result = "(short) 0";
			}
			else if(type.equals("int")){
				result = "0";
			}
			else if(type.equals("long")){
				result = "0L";
			}
			else if(type.equals("float")){
				result = "0.0f";
			}
			else if(type.equals("double")){
				result = "0.0d";
			}
			else if(type.equals("char")){
				result = "(char) 0";
			}
			else{
				result = "null";
			}
		}
		return result;
	}
}
