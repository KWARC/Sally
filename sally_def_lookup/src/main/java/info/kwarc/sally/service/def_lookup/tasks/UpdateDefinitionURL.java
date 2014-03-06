package info.kwarc.sally.service.def_lookup.tasks;

import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.service.def_lookup.DefinitionLookupService;

import com.google.inject.Inject;

@SallyTask(action="UpdateDefinitionURL")
public class UpdateDefinitionURL implements WorkItemHandler {
	DefinitionLookupService planetary;
	
	@Inject
	public UpdateDefinitionURL(DefinitionLookupService planetary) {
		this.planetary = planetary;
	}
	
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String mmtURI = workItem.getFirstTypedParameter(String.class);
		try {
			if (mmtURI == null)
				throw new Exception("No MMT URI given");
			String url = planetary.getDefinitionLookupURL(mmtURI);	
			workItem.addResult("DefURLOutput", url);
		} catch (Exception e) {
			
		} finally {
			manager.completeWorkItem(workItem);
		}
		
	}

	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
