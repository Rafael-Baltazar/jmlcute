package org.jmlspecs.lang.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface CapturesDefinitions {
  Captures[] value() default {};
}
