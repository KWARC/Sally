package info.kwarc.sally.core;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
public @interface SallyService {
	boolean overwrite() default false;
	String channel() default "/what";
}
