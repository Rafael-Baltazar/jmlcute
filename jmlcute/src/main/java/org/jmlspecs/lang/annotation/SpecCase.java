package org.jmlspecs.lang.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface SpecCase {
  /** tag format: (('+'|'-')? JavaId) (',' ('+'|'-') JavaId)*)? */
  String tag()				                  default "";
  String header()			                  default "";
  String modelProgram()			              default "";
  // JML clauses
  Requires[] requiresDefinitions()            default {};
  Assignable[] assignableDefinitions()        default {};
  Ensures[] ensuresDefinitions()              default {};
  Signals[] signalsDefinitions()              default {};
  SignalsOnly[] signalsOnlyDefinitions()      default {};
  Callable[] callableDefinitions()            default {};
  Accessible[] accessibleDefinitions()        default {};
  Duration[] durationDefinitions()            default {};
  Captures[] capturesDefinitions()            default {};
  WorkingSpace[] workingSpaceDefinitions()    default {};
}
