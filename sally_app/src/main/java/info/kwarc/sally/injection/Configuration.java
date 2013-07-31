package info.kwarc.sally.injection;

import org.slf4j.Logger;

import info.kwarc.sally.ConnectionManager;
import info.kwarc.sally.PricingService;
import info.kwarc.sally.ProcessDocMappings;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sally.planetary.injection.PlanetaryModule;
import info.kwarc.sally.spreadsheet.injection.SpreadsheetModule;
import info.kwarc.sally.theofx.TheoService;
import info.kwarc.sally.utils.LoggerProvider;
import info.kwarc.sissi.model.document.cad.injection.CADModule;

import com.google.inject.AbstractModule;
import com.google.inject.name.Names;

public class Configuration extends AbstractModule {

	@Override
	protected void configure() {
		install(new SpreadsheetModule());
		install(new CADModule());
		install(new PlanetaryModule());
		
		bind(ConnectionManager.class);
		bind(SallyInteraction.class);
		bind(PricingService.class);
		bind(ProcessDocMappings.class);
		bind(Logger.class).toProvider(LoggerProvider.class);		
		
		bind(String[].class).annotatedWith(Names.named("BPMN Files")).toInstance(
					new String[]{"bpmn/connect.bpmn", "bpmn/document_creator.bpmn"});
		
		bind(Theo.class).to(TheoService.class);
		
		bind(String.class).annotatedWith(Names.named("PlanetaryURL")).toInstance("http://localhost/planetary");
		bind(String.class).annotatedWith(Names.named("PlanetaryEndPoint")).toInstance("sallyrpc");  
		bind(String.class).annotatedWith(Names.named("PlanetaryUser")).toInstance("sally"); 
		bind(String.class).annotatedWith(Names.named("PLanetaryPassword")).toInstance("123"); 
		
		bind(String.class).annotatedWith(Names.named("KnowledgePackageURL")).toInstance("http://localhost:8080/drools-guvnor/org.drools.guvnor.Guvnor/package/Sally/LATEST");
		bind(String.class).annotatedWith(Names.named("KnowledgeBaseUser")).toInstance("admin");
		bind(String.class).annotatedWith(Names.named("KnowledgeBasePassword")).toInstance("admin");
	}

}
