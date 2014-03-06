package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.LocalBPMNKnowledgeBase;

public class ProductionLocalKnowledgeBase extends JBPM {
	
	@Override
	protected void configure() {
		super.configure();
		bind(ISallyWorkflowManager.class).to(LocalBPMNKnowledgeBase.class);
	}
	
}
