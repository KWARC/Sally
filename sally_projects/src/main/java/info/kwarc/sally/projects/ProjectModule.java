package info.kwarc.sally.projects;

import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

@SallyTask(action="ShowProjectFiles")
public class ProjectModule implements WorkItemHandler{
	String filePath;
	ProjectModel data;
	INetworkSender sender;
	
	@Inject
	public ProjectModule(@Assisted String filePath, @Assisted ProjectModel data, @Assisted INetworkSender networkSender) {
		this.filePath = filePath;
		this.data = data;
		this.sender = networkSender;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}
	
	
}
