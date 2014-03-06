package info.kwarc.sissi.bpm;

import info.kwarc.sally.core.workflow.WorkItemHandler;

import java.util.HashMap;
import java.util.Map;

import org.drools.KnowledgeBase;
import org.drools.builder.KnowledgeBuilder;
import org.drools.builder.KnowledgeBuilderFactory;
import org.drools.builder.ResourceType;
import org.drools.io.ResourceFactory;
import org.drools.io.impl.UrlResource;
import org.drools.logger.KnowledgeRuntimeLogger;
import org.drools.logger.KnowledgeRuntimeLoggerFactory;
import org.drools.runtime.StatefulKnowledgeSession;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

@Singleton
public class RemotePkgKnowledgeBase extends AbstractKnowledgeBase {
	KnowledgeBuilder kbuilder;
	KnowledgeBase kb;
	StatefulKnowledgeSession ksession;
	
	HashMap<String, Class<? extends WorkItemHandler>> handlerClasses;
	final Map<String, WorkItemHandler> handlerInstances; 
	KnowledgeRuntimeLogger klogger;
	Injector injector;

	@Inject
	public RemotePkgKnowledgeBase(
			@Named("WorkItemHandlers") HashMap<String, Class<? extends WorkItemHandler>> handlerClasses,
			@Named("KnowledgePackageURL") String sallyPackage, 
			@Named("KnowledgeBaseUser") String kbUser, 
			@Named("KnowledgeBasePassword") String kbPassword,
			Injector injector) {
		
		this.injector = injector;
		
		UrlResource standardUrlResource = (UrlResource)ResourceFactory.newUrlResource(sallyPackage);
		standardUrlResource.setBasicAuthentication("enabled");
		standardUrlResource.setUsername(kbUser);
		standardUrlResource.setPassword(kbPassword);
		
		handlerInstances = new HashMap<String, WorkItemHandler>();
		this.handlerClasses = handlerClasses;

		kbuilder = KnowledgeBuilderFactory.newKnowledgeBuilder();
		kbuilder.add(standardUrlResource, ResourceType.PKG);
		init();
	}
	
	public void init() {
		kb = kbuilder.newKnowledgeBase();
		ksession = kb.newStatefulKnowledgeSession();
		registerTasks(ksession, handlerClasses, handlerInstances, injector);
		klogger = KnowledgeRuntimeLoggerFactory.newThreadedFileLogger(ksession, "session", 500);
	}

	@Override
	protected StatefulKnowledgeSession getSession() {
		return ksession;
	}
}
