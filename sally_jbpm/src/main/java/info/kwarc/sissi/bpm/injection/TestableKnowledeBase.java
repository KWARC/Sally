package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.AbstractKnowledgeBase;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import org.drools.runtime.StatefulKnowledgeSession;

import com.google.inject.AbstractModule;
import com.google.inject.Inject;
import com.google.inject.Singleton;

public class TestableKnowledeBase extends AbstractModule {

	StatefulKnowledgeSession knowledgeSession;

	public TestableKnowledeBase(StatefulKnowledgeSession testCase) {
		this.knowledgeSession = testCase;
	}

	@Singleton
	static class JUnitKnowledge extends AbstractKnowledgeBase {
		StatefulKnowledgeSession ksession;

		@Inject
		public JUnitKnowledge(
				StatefulKnowledgeSession ksession) {
			this.ksession = ksession;
		}

		@Override
		protected StatefulKnowledgeSession getSession() {
			return ksession;
		}
	}

	@Override
	protected void configure() {
		bind(StatefulKnowledgeSession.class).toInstance(knowledgeSession);
		bind(ISallyKnowledgeBase.class).to(JUnitKnowledge.class);
	}

}
