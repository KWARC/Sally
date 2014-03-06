package info.kwarc.sally.core.workflow;

import java.util.Map;

public interface WorkItem {
	Map<String, Object> getParameters();
	Map<String, Object> getProcessVariables();
	<T> T getFirstTypedParameter(Class<T> cls);
	Long getProcessInstanceId();
	Long getWorkItemId();
	
	void addResult(String key, Object value);
	Map<String, Object> getResults();
}
