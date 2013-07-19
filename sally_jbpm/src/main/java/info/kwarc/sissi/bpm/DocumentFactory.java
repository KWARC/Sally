package info.kwarc.sissi.bpm;

import info.kwarc.sally.core.SallyAction;
import info.kwarc.sally.core.interfaces.SallyTask;

import java.util.Map;

import sally.SemanticData;
import sally.WhoAmI;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
@SallyTask(action="info.kwarc.sally.connectDoc")
public class DocumentFactory implements SallyAction {

	SallyKnowledgeBase knowledgeBase;
	
	@Inject
	public DocumentFactory(SallyKnowledgeBase knowledgeBase) {
		this.knowledgeBase = knowledgeBase;
	}
	
	public void test() {
		
	}

	@Override
	public void run(Map<String, Object> parameters) {
		WhoAmI alexInfo = (WhoAmI) parameters.get("alexInfo");
		SemanticData semanticData = (SemanticData) parameters.get("docSemantics");
		System.out.println("creating "+ alexInfo);
		
		knowledgeBase.getKnowledgeSession().createProcessInstance("", parameters);
	}
	
}
