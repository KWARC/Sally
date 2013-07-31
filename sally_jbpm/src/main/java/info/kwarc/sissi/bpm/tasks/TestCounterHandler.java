package info.kwarc.sissi.bpm.tasks;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

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
		manager.completeWorkItem(workItem.getId(), null);
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		executed++;
		manager.completeWorkItem(workItem.getId(), null);
	}
}
