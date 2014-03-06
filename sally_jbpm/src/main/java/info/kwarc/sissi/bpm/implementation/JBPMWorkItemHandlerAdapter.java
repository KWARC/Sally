package info.kwarc.sissi.bpm.implementation;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.WorkItemHandler;

import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

public class JBPMWorkItemHandlerAdapter implements org.drools.process.instance.WorkItemHandler{
	WorkItemHandler handler;
	ISallyWorkflowManager workflowManager;
	
	public JBPMWorkItemHandlerAdapter(WorkItemHandler handler, ISallyWorkflowManager workflowManager) {
		this.handler = handler;
		this.workflowManager = workflowManager;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		handler.executeWorkItem(new JBPMWorkItemAdapter(workItem, workflowManager), new JBPMWorkItemManagerAdapter(manager));
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		handler.abortWorkItem(new JBPMWorkItemAdapter(workItem, workflowManager), new JBPMWorkItemManagerAdapter(manager));		
	}
}
