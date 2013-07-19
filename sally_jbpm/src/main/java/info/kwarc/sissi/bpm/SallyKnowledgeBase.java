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
public class SallyKnowledgeBase implements ISallyKnowledgeBase {

	StatefulKnowledgeSession ksession;
	KnowledgeBase kbase;
	KnowledgeRuntimeLogger klogger;
	
	Map<String, WorkItemHandler> handlers; 

	String sallyPackage = "http://localhost:8080/drools-guvnor/org.drools.guvnor.Guvnor/package/Sally/Sally.drl";

	@Inject
	public SallyKnowledgeBase(
			@Named("DynamicApplicability") WorkItemHandler dynamicApplicability,
			@Named("SallyTask") WorkItemHandler sallyTask,
			@Named("BPMN Files") String [] files
		) {

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
		/*
		UrlResource standardUrlResource = (UrlResource)ResourceFactory.newUrlResource(sallyPackage);
		standardUrlResource.setBasicAuthentication("enabled");
		standardUrlResource.setUsername("admin");
		standardUrlResource.setPassword("admin");
		 */	
		kbuilder.add(ResourceFactory.newClassPathResource("connect.bpmn"), ResourceType.BPMN2);
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

}
