package info.kwarc.sissi.bpm.inferfaces;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;

public interface ISallyKnowledgeBase {
	StatefulKnowledgeSession getKnowledgeSession();
	ProcessInstance startProcess(String processID);
}
