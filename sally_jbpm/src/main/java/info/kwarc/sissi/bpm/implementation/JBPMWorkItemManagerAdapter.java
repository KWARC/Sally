package info.kwarc.sissi.bpm.implementation;

import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemManager;

public class JBPMWorkItemManagerAdapter implements WorkItemManager{
	org.drools.runtime.process.WorkItemManager  handler;
	
	public JBPMWorkItemManagerAdapter(org.drools.runtime.process.WorkItemManager manager) {
		this.handler = manager;
	}

	@Override
	public void completeWorkItem(WorkItem workItem) {
		handler.completeWorkItem(workItem.getWorkItemId(), workItem.getResults());
	}
}
