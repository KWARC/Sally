package info.kwarc.sally.theoweb.injection;

import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.theoweb.WebTheo;

import com.google.inject.AbstractModule;
import com.google.inject.name.Names;

public class WebTheoModule extends AbstractModule {

	@Override
	protected void configure() {
		bind(Theo.class).annotatedWith(Names.named("WebTheo")).to(WebTheo.class);
	}

}
