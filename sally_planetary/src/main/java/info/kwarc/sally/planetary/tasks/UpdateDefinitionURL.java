package info.kwarc.sally.planetary.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

import com.google.inject.Inject;

@SallyTask(action="UpdateDefinitionURL")
public class UpdateDefinitionURL implements WorkItemHandler {
	Planetary planetary;
	
	@Inject
	public UpdateDefinitionURL(Planetary planetary) {
		this.planetary = planetary;
	}
	
	@Override
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

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
