package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.LocalBPMNKnowledgeBase;

import com.google.inject.AbstractModule;

public class ProductionLocalKnowledgeBase extends AbstractModule {
	
	@Override
	protected void configure() {
		bind(ISallyWorkflowManager.class).to(LocalBPMNKnowledgeBase.class);
	}
	
}
