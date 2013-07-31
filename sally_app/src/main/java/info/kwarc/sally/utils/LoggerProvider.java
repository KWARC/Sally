package info.kwarc.sally.utils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Provider;

public class LoggerProvider implements Provider<Logger>{

	@Override
	public Logger get() {
		return LoggerFactory.getLogger(this.getClass());
	}
}
