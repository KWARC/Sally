package info.kwarc.sally.theofx.injection;

import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sally.theofx.TheoService;
import info.kwarc.sally.theofx.interfaces.ITheoAppProvider;
import info.kwarc.sally.theofx.interfaces.ITheoWindowProvider;
import info.kwarc.sally.theofx.tasks.TheoWindowCreate;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class TheoFX extends AbstractModule {

	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(ITheoAppProvider.class));
		install(new FactoryModuleBuilder().build(ITheoWindowProvider.class));

		bind(Theo.class).to(TheoService.class);
		bind(TheoWindowCreate.class);
		
	}

}
