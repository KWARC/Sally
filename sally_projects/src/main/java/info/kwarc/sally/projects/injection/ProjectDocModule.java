package info.kwarc.sally.projects.injection;

import info.kwarc.sally.projects.ProjectFactory;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class ProjectDocModule  extends AbstractModule {
	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(ProjectFactory.class));
	}
}
