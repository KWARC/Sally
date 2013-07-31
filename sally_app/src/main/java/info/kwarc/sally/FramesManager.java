package info.kwarc.sally;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.awt.MenuItem;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.MMTUri;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class FramesManager {
	Logger log;

	ISallyKnowledgeBase knowledgeBase;
	SallyInteraction interaction;

	@Inject
	public FramesManager(ISallyKnowledgeBase knowledgeBase, SallyInteraction interaction) throws Exception {
		this.knowledgeBase = knowledgeBase;
		log = LoggerFactory.getLogger(this.getClass());
		this.interaction = interaction;
	}
	
	public List<SallyMenuItem>  getFrames(String objectURI) {
		MMTUri mmtURI = MMTUri.newBuilder().setUri(objectURI).build();
		return interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class);
	}

}
