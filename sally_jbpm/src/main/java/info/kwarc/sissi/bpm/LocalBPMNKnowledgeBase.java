package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

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
import org.drools.runtime.process.ProcessInstance;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

@Singleton
public class LocalBPMNKnowledgeBase implements ISallyKnowledgeBase {

	StatefulKnowledgeSession ksession;
	KnowledgeBase kbase;
	KnowledgeRuntimeLogger klogger;
	String files[];
	
	Map<String, WorkItemHandler> handlers; 

	@Inject
	public LocalBPMNKnowledgeBase(
			@Named("DynamicApplicability") WorkItemHandler dynamicApplicability,
			@Named("SallyTask") WorkItemHandler sallyTask,
			@Named("BPMN Files") String [] files
		) {

		this.files = files;
		handlers = new HashMap<String, WorkItemHandler>();
		handlers.put("DynamicApplicability", dynamicApplicability);
		handlers.put("SallyTask", sallyTask);
		ksession = null;
	}

	private void initIfNecessary() {
		if (ksession == null) {
			try {
				init();
			} catch (Exception e) {
				e.printStackTrace();
			}
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
		for (String file : files) {
			kbuilder.add(ResourceFactory.newClassPathResource(file), ResourceType.BPMN2);
		}
		return kbuilder.newKnowledgeBase();
	}

	@Override
	public StatefulKnowledgeSession getKnowledgeSession() {
		initIfNecessary();
		return ksession;
	}

	@Override
	public ProcessInstance startProcess(String processID) {
		initIfNecessary();
		if (ksession == null)
			return null;
		return ksession.startProcess(processID);
	}

	@Override
	public ProcessInstance startProcess(String processID, Map<String, Object> obj) {
		initIfNecessary();
		if (ksession == null)
			return null;
		return ksession.startProcess(processID, obj);
	}

}
