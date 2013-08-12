package info.kwarc.sissi.bpm;

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
import org.drools.process.instance.WorkItemHandler;
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

	Map<String, WorkItemHandler> handlers; 
	KnowledgeRuntimeLogger klogger;


	@Inject
	public RemotePkgKnowledgeBase(
			@Named("WorkItemHandlers") HashMap<String, Class<? extends WorkItemHandler>> handlerClasses,
			@Named("KnowledgePackageURL") String sallyPackage, 
			@Named("KnowledgeBaseUser") String kbUser, 
			@Named("KnowledgeBasePassword") String kbPassword,
			Injector injector) {
		
		UrlResource standardUrlResource = (UrlResource)ResourceFactory.newUrlResource(sallyPackage);
		standardUrlResource.setBasicAuthentication("enabled");
		standardUrlResource.setUsername(kbUser);
		standardUrlResource.setPassword(kbPassword);
		
		handlers = new HashMap<String, WorkItemHandler>();
		for (String taskName : handlerClasses.keySet()) {
			handlers.put(taskName, injector.getInstance(handlerClasses.get(taskName)));
		}

		kbuilder = KnowledgeBuilderFactory.newKnowledgeBuilder();
		kbuilder.add(standardUrlResource, ResourceType.PKG);
		init();
	}
	
	public void init() {
		kb = kbuilder.newKnowledgeBase();
		ksession = kb.newStatefulKnowledgeSession();
		for (String k : handlers.keySet()) {
			ksession.getWorkItemManager().registerWorkItemHandler(k, handlers.get(k));
		}
		klogger = KnowledgeRuntimeLoggerFactory.newThreadedFileLogger(ksession, "session", 500);
	}

	@Override
	protected StatefulKnowledgeSession getSession() {
		return ksession;
	}
}
