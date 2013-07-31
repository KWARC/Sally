package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.LocalBPMNKnowledgeBase;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import com.google.inject.AbstractModule;

public class ProductionLocalKnowledgeBase extends AbstractModule {
	
	@Override
	protected void configure() {
		bind(ISallyKnowledgeBase.class).to(LocalBPMNKnowledgeBase.class);
	}
	
}
