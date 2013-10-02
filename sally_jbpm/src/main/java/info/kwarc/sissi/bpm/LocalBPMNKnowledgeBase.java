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
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

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
	Injector injector;
	HashMap<String, Class<? extends WorkItemHandler>> handlerClasses;
	final Map<String, WorkItemHandler> handlerInstances; 
	
	Map<String, WorkItemHandler> handlers; 

	@Inject
	public LocalBPMNKnowledgeBase(
			@Named("WorkItemHandlers") HashMap<String, Class<? extends WorkItemHandler>> handlerClasses,
			@Named("SallyPackage") String file,
			Injector injector
		) {
		this.injector = injector;

		handlerInstances = new HashMap<String, WorkItemHandler>();
		this.handlerClasses = handlerClasses;
		
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
		
		for (final String taskName : handlerClasses.keySet()) {
			ksession.getWorkItemManager().registerWorkItemHandler(taskName, new org.drools.runtime.process.WorkItemHandler() {
				
				@Override
				public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
					if (!handlerInstances.containsKey(taskName)) {
						handlerInstances.put(taskName, injector.getInstance(handlerClasses.get(taskName)));
					}
					handlerInstances.get(taskName).executeWorkItem(workItem, manager);
				}
				
				@Override
				public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
					if (!handlerInstances.containsKey(taskName)) {
						handlerInstances.put(taskName, injector.getInstance(handlerClasses.get(taskName)));
					}
					handlerInstances.get(taskName).executeWorkItem(workItem, manager);
				}
			});
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
