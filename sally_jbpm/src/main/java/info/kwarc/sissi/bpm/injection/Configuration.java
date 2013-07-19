package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.ConnectionManager;

import com.google.inject.AbstractModule;
import com.google.inject.name.Names;

public class Configuration extends AbstractModule {

	@Override
	protected void configure() {
		bind(ConnectionManager.class);
		
		bind(String[].class).annotatedWith(Names.named("BPMN Files")).toInstance(
					new String[]{"connect.bpmn"});
	}

}
