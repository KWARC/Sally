package info.kwarc.sally.sketch.injection;

import info.kwarc.sally.sketch.SketchFactory;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class SketchDocModule  extends AbstractModule {
	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(SketchFactory.class));
	}
}
