package info.kwarc.sissi.bpm.injection;

import info.kwarc.sissi.bpm.RemotePkgKnowledgeBase;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import com.google.inject.AbstractModule;

public class ProductionRemoteKnowledgeBase extends AbstractModule {
	
	@Override
	protected void configure() {
		bind(ISallyKnowledgeBase.class).to(RemotePkgKnowledgeBase.class);
	}
	
}
