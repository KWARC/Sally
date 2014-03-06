package info.kwarc.sally.core.workflow;

import java.util.List;
import java.util.Map;

public interface ISallyWorkflowManager {
	ProcessInstance startProcess(Long parentProcessInstanceID, String processID);
	ProcessInstance startProcess(Long parentProcessInstanceID, String processID, Map<String, Object> obj);
	void startProcess(ProcessInstance pi);

	ProcessInstance prepareProcess(Long parentProcessInstanceID, String processID);
	ProcessInstance prepareProcess(Long parentProcessInstanceID, String processID, Map<String, Object> obj);

	
	Long getWorkflowParent(Long processInstanceID);
	List<Long> getWorkflowChildren(Long processInstanceID);
	
	ProcessInstance getProcessInstance(Long processinstanceID);
	void registerWorkItemHandler(String Name, WorkItemHandler handler);
	void signal_global_event(String signal_ref, Object data);
	
	boolean propagateParentMessage(Long currentProcessInstanceID, String message_id, Object input);
	boolean propagateChildMessage(Long currentProcessInstanceID, String message_id, Object input);
}
