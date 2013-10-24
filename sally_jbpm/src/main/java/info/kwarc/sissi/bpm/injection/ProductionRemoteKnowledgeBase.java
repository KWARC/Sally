package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.RemotePkgKnowledgeBase;

import com.google.inject.AbstractModule;

public class ProductionRemoteKnowledgeBase extends AbstractModule {
	
	@Override
	protected void configure() {
		bind(ISallyWorkflowManager.class).to(RemotePkgKnowledgeBase.class);
	}
	
}
