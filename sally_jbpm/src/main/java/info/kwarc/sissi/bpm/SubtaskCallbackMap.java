package info.kwarc.sissi.bpm;

import java.util.HashMap;

import com.google.inject.Singleton;

@Singleton
public class SubtaskCallbackMap {

	HashMap <Long, Long> workflowCallbackMap;
	
	public SubtaskCallbackMap() {
		workflowCallbackMap  = new HashMap<Long, Long>();
	}
	
	public void registerCallbackForWorkflow(Long workflowID, Long callbackID) {
		workflowCallbackMap.put(workflowID, callbackID);
	}
	
	public Long getWorkflowSubtask(Long workflowID) {
		return workflowCallbackMap.get(workflowID);
	}
}
