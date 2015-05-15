// Generated from RacMessages.msg
package org.jmlspecs.ajmlrac;

import org.multijava.util.MessageDescription;

public class RacMessages {
  public static final MessageDescription	RAC_GEN = new MessageDescription("[ generated runtime assertion check code in {0} ms ]", null, 6);
  public static final MessageDescription	RECURSIVELY_REFERENCED_TYPE = new MessageDescription("Can not determine the exact model field denoted by the identifier \"{0}\" of a potentially applicable represents clause. Please, compile again either by explicitly listing this source file in the command-line or by specifying the command-line flag --recursiveType (-t) to force typechecking of recursively referenced type \"{1}\".", null, 0);
  public static final MessageDescription	NOT_SUPPORTED = new MessageDescription("The JML RAC does not support {0}.", null, 0);
  public static final MessageDescription	MAY_NOT_EXECUTABLE = new MessageDescription("{0} may not be executable.", null, 2);
  public static final MessageDescription	NOT_EXECUTABLE = new MessageDescription("{0} is not executable.", null, 2);
  public static final MessageDescription	NOT_SUPPORTED_ALT = new MessageDescription("{0} is not supported by the RAC using this command-line option. Entire clause will be dropped and assume to be \"true\".", null, 2);
}
