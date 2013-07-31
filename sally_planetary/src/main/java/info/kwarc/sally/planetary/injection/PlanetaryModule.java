package info.kwarc.sally.planetary.injection;

import info.kwarc.sally.planetary.Planetary;

import com.google.inject.AbstractModule;

public class PlanetaryModule extends AbstractModule {

	@Override
	protected void configure() {
		bind(Planetary.class);
	}
}
