package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;

import com.google.inject.AbstractModule;
import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

public class TestableKnowledeBase extends AbstractModule {

	StatefulKnowledgeSession knowledgeSession;

	public TestableKnowledeBase(StatefulKnowledgeSession testCase) {
		this.knowledgeSession = testCase;
	}

	@Singleton
	static class JUnitKnowledge implements ISallyKnowledgeBase {
		StatefulKnowledgeSession ksession;

		@Inject
		public JUnitKnowledge(
				@Named("DynamicApplicability") WorkItemHandler dynamicApplicability,
				@Named("SallyTask") WorkItemHandler sallyTask,
				StatefulKnowledgeSession ksession) {
			this.ksession = ksession;

			ksession.getWorkItemManager().registerWorkItemHandler("DynamicApplicability", dynamicApplicability);
			ksession.getWorkItemManager().registerWorkItemHandler("SallyTask", sallyTask);
		}

		@Override
		public StatefulKnowledgeSession getKnowledgeSession() {
			return ksession;
		}

		@Override
		public ProcessInstance startProcess(String processID) {
			return ksession.startProcess(processID);
		}
	}

	@Override
	protected void configure() {
		bind(StatefulKnowledgeSession.class).toInstance(knowledgeSession);
		bind(ISallyKnowledgeBase.class).to(JUnitKnowledge.class);
	}

}
