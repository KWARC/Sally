package info.kwarc.sissi.bpm;

import java.util.HashMap;
import java.util.Map;

import org.drools.KnowledgeBase;
import org.drools.builder.KnowledgeBuilder;
import org.drools.builder.KnowledgeBuilderFactory;
import org.drools.builder.ResourceType;
import org.drools.io.ResourceFactory;
import org.drools.logger.KnowledgeRuntimeLogger;
import org.drools.logger.KnowledgeRuntimeLoggerFactory;
import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.StatefulKnowledgeSession;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

@Singleton
public class LocalBPMNKnowledgeBase extends AbstractKnowledgeBase {

	StatefulKnowledgeSession ksession;
	KnowledgeBase kbase;
	KnowledgeRuntimeLogger klogger;
	String file;
	
	Map<String, WorkItemHandler> handlers; 

	@Inject
	public LocalBPMNKnowledgeBase(
			@Named("WorkItemHandlers") HashMap<String, Class<? extends WorkItemHandler>> handlerClasses,
			@Named("SallyPackage") String file,
			Injector injector
		) {

		handlers = new HashMap<String, WorkItemHandler>();
		for (String taskName : handlerClasses.keySet()) {
			handlers.put(taskName, injector.getInstance(handlerClasses.get(taskName)));
		}
		
		this.file = file;
		ksession = null;
		try {
			init();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void init() throws Exception {
		kbase = readKnowledgeBase();
		ksession = kbase.newStatefulKnowledgeSession();
		for (String k : handlers.keySet()) {
			ksession.getWorkItemManager().registerWorkItemHandler(k, handlers.get(k));
		}
		klogger = KnowledgeRuntimeLoggerFactory.newThreadedFileLogger(ksession, "session", 500);
	}
	
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		klogger.close();
	}

	
	KnowledgeBase readKnowledgeBase() throws Exception {
		KnowledgeBuilder kbuilder = KnowledgeBuilderFactory.newKnowledgeBuilder();
		kbuilder.add(ResourceFactory.newClassPathResource(file), ResourceType.PKG);
		return kbuilder.newKnowledgeBase();
	}

	@Override
	protected StatefulKnowledgeSession getSession() {
		return ksession;
	}

}
