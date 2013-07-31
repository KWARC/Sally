package info.kwarc.sally.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

@SallyTask(action="InitTheo")
public class InitTheo implements WorkItemHandler {

	public InitTheo() {
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem.getId(), null);
	}
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem.getId(), null);
	}
}
