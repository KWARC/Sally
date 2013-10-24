package info.kwarc.sally.html.injection;

import info.kwarc.sally.html.HTMLFactory;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class HTMLDocModule  extends AbstractModule {
	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(HTMLFactory.class));
	}
}
