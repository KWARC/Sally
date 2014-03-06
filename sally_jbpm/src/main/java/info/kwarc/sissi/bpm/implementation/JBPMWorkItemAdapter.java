package info.kwarc.sissi.bpm.implementation;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkflowUtils;

import java.util.Map;

public class JBPMWorkItemAdapter implements WorkItem{
	org.drools.runtime.process.WorkItem  handler;
	ISallyWorkflowManager workflowManager;
	
	public JBPMWorkItemAdapter(org.drools.runtime.process.WorkItem handler, ISallyWorkflowManager workflowManager) {
		this.workflowManager  = workflowManager;
		this.handler = handler;
	}

	@Override
	public Map<String, Object> getParameters() {
		return handler.getParameters();
	}

	@Override
	public Map<String, Object> getProcessVariables() {
		return workflowManager.getProcessInstance(handler.getProcessInstanceId()).getProcessVariables();
	}

	@Override
	public <T> T getFirstTypedParameter(Class<T> cls) {
		return WorkflowUtils.getFirstTypedParameter(handler.getParameters(), cls);
	}

	@Override
	public Long getProcessInstanceId() {
		return handler.getProcessInstanceId();
	}

	@Override
	public void addResult(String key, Object value) {
		handler.getResults().put(key, value);
	}

	@Override
	public Long getWorkItemId() {
		return handler.getId();
	}

	@Override
	public Map<String, Object> getResults() {
		return handler.getResults();
	}

}
