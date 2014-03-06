package info.kwarc.sally.bpm.tasks;

import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

public class TestCounterHandler implements WorkItemHandler {
	int executed;
	int aborted;
	
	public int getAborted() {
		return aborted;
	}
	
	public int getExecuted() {
		return executed;
	}
	
	public TestCounterHandler() {
		executed = 0;
		aborted = 0;
	}
	
	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		aborted ++;
		manager.completeWorkItem(workItem);
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		executed++;
		manager.completeWorkItem(workItem);
	}
}
