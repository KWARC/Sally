package info.kwarc.sally.theofx.injection;

import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.theo.tasks.TheoWindowCreate;
import info.kwarc.sally.theofx.TheoService;
import info.kwarc.sally.theofx.interfaces.ITheoAppProvider;
import info.kwarc.sally.theofx.interfaces.ITheoWindowProvider;
import info.kwarc.sally.theofx.tasks.TheoFXWindowCreate;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;
import com.google.inject.name.Names;

public class TheoFX extends AbstractModule {

	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(ITheoAppProvider.class));
		install(new FactoryModuleBuilder().build(ITheoWindowProvider.class));

		bind(Theo.class).annotatedWith(Names.named("DesktopTheo")).to(TheoService.class);
		bind(TheoWindowCreate.class).annotatedWith(Names.named("DesktopTheo")).to(TheoFXWindowCreate.class);
		
	}

}
