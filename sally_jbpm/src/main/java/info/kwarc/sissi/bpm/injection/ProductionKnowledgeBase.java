package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.SallyKnowledgeBase;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import com.google.inject.AbstractModule;

public class ProductionKnowledgeBase extends AbstractModule {
	
	@Override
	protected void configure() {
		bind(ISallyKnowledgeBase.class).to(SallyKnowledgeBase.class);
	}
	
}
