package info.kwarc.sally.projects;

import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.workflow.SallyTask;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

import sally.ProjectModel;

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
