package info.kwarc.sally.core.workflow;

public interface WorkItemHandler {
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) ;
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager);
}
