package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.util.Map;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;

import com.google.inject.AbstractModule;
import com.google.inject.Inject;
import com.google.inject.Singleton;

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
				StatefulKnowledgeSession ksession) {
			this.ksession = ksession;
		}

		@Override
		public StatefulKnowledgeSession getKnowledgeSession() {
			return ksession;
		}

		@Override
		public ProcessInstance startProcess(String processID) {
			return ksession.startProcess(processID);
		}

		@Override
		public ProcessInstance startProcess(String processID,
				Map<String, Object> obj) {
			return ksession.startProcess(processID, obj);
		}
	}

	@Override
	protected void configure() {
		bind(StatefulKnowledgeSession.class).toInstance(knowledgeSession);
		bind(ISallyKnowledgeBase.class).to(JUnitKnowledge.class);
	}

}
