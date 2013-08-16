package info.kwarc.sissi.bpm.inferfaces;

import java.util.Map;

import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItemHandler;

public interface ISallyKnowledgeBase {
	ProcessInstance startProcess(Long parentProcessInstanceID, String processID);
	ProcessInstance startProcess(Long parentProcessInstanceID, String processID, Map<String, Object> obj);
	
	ProcessInstance getProcessInstance(Long processinstanceID);
	void registerWorkItemHandler(String Name, WorkItemHandler handler);
	void signal_global_event(String signal_ref, Object data);
	
	boolean propagateParentMessage(Long currentProcessInstanceID, String message_id, Object input);
}
