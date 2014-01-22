package info.kwarc.sally.service.def_lookup.tasks;

import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.service.def_lookup.DefinitionLookupService;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

import com.google.inject.Inject;

@SallyTask(action="UpdateDefinitionURL")
public class UpdateDefinitionURL implements WorkItemHandler {
	DefinitionLookupService planetary;
	
	@Inject
	public UpdateDefinitionURL(DefinitionLookupService planetary) {
		this.planetary = planetary;
	}
	
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String mmtURI = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		try {
			if (mmtURI == null)
				throw new Exception("No MMT URI given");
			String url = planetary.getDefinitionLookupURL(mmtURI);	
			workItem.getResults().put("DefURLOutput", url);
		} catch (Exception e) {
			
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
		
	}

	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
