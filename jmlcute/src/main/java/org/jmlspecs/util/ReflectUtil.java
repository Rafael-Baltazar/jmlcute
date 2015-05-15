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
 * $Id: ReflectUtil.java,v 1.0 2013/05/17 11:37:06 henriquerebelo Exp $
 */

package org.jmlspecs.util;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;

public class ReflectUtil {
	
	// java.lang.reflect Constructor Util - [[[hemr]]]
	public static String getConstructorSignatureWithLongTypeNames ( Constructor<?> init ) {
		return getSignature(init, true);
	}

	public static String getConstructorSignatureWithShortTypeNames ( Constructor<?> init ) {
		return getSignature(init, false);
	}

    // java.lang.reflect Method Util - [[[hemr]]]
	public static String getMethodSignatureWithLongTypeNames ( Method method ) {
		return getSignature(method, true);
	}

	public static String getMethodSignatureWithShortTypeNames ( Method method ) {
		return getSignature(method, false);
	}
	

	// helper methods - [[[hemr]]]
	private static String getSignature ( Constructor<?> init, boolean longTypeNames ) {
		return init.getName() + "("+ parametersAsString(init, longTypeNames) + ")";
	}
	
	private static String parametersAsString ( Constructor<?> init, boolean longTypeNames ) {
		String result = "";
		Class<?>[] parameterTypes = init.getParameterTypes();
		if ( parameterTypes.length > 0 ) {
			StringBuilder paramString = new StringBuilder();
			paramString.append(longTypeNames ? parameterTypes[0].getName()
					: parameterTypes[0].getSimpleName());
			for ( int i = 1 ; i < parameterTypes.length ; i++ ) {
				paramString.append(",").append(
						longTypeNames  ? parameterTypes[i].getName()
								: parameterTypes[i].getSimpleName());
			}
			result = paramString.toString();
		}
		return result;
	}	
	
	private static String getSignature ( Method method, boolean longTypeNames ) {
		return method.getName() + "("+ parametersAsString(method, longTypeNames) + ")";
	}

	private static String parametersAsString ( Method method, boolean longTypeNames ) {
		String result = "";
		Class<?>[] parameterTypes = method.getParameterTypes();
		if ( parameterTypes.length > 0 ) {
			StringBuilder paramString = new StringBuilder();
			paramString.append(longTypeNames ? parameterTypes[0].getName()
					: parameterTypes[0].getSimpleName());
			for ( int i = 1 ; i < parameterTypes.length ; i++ ) {
				paramString.append(",").append(
						longTypeNames  ? parameterTypes[i].getName()
								: parameterTypes[i].getSimpleName());
			}
			result = paramString.toString();
		}
		return result;
	}	

}
