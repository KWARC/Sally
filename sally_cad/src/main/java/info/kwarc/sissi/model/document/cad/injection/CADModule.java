package info.kwarc.sissi.model.document.cad.injection;

import info.kwarc.sissi.model.document.cad.interfaces.CADFactory;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class CADModule extends AbstractModule{

	@Override
	protected void configure() {
		install(new FactoryModuleBuilder()
	     .build(CADFactory.class));
	}
	
}
