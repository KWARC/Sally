package info.kwarc.sally.networking.Injection;

import info.kwarc.sally.networking.CometD;
import info.kwarc.sally.networking.TemplateEngine;
import info.kwarc.sally.networking.interfaces.IConnectionPlayerFactory;
import info.kwarc.sally.networking.interfaces.INetworkSenderAdapter;

import java.util.HashMap;
import java.util.Map;

import com.google.inject.assistedinject.FactoryModuleBuilder;
import com.google.inject.servlet.GuiceFilter;
import com.google.inject.servlet.ServletModule;
import com.sun.jersey.api.core.PackagesResourceConfig;
import com.sun.jersey.guice.spi.container.servlet.GuiceContainer;

public class ProductionNetworking extends ServletModule {

	@Override
	protected void configureServlets() {
        bind(GuiceFilter.class).asEagerSingleton();

        bind(INetworkSenderAdapter.class).toProvider(CometD.class);
        
		install(new FactoryModuleBuilder()
		.build(IConnectionPlayerFactory.class));	
		
		 // hook Jersey into Guice Servlet
        bind(GuiceContainer.class);

        // hook Jackson into Jersey as the POJO <-> JSON mapper
        //bind(JacksonJsonProvider.class).in(Scopes.SINGLETON);

        Map<String, String> params = new HashMap<String, String>();
        params.put(PackagesResourceConfig.PROPERTY_PACKAGES, "info.kwarc.sally");
        serve("/*").with(GuiceContainer.class, params);
        
		bind(TemplateEngine.class);
	}
}
