package info.kwarc.sally.theofx.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="theoWindowUpdate")
public class TheoWindowUpdate implements WorkItemHandler{

	Logger log;
	Theo theo;
	
	@Inject
	public TheoWindowUpdate(Theo theo) {
		log = LoggerFactory.getLogger(getClass());
		this.theo = theo;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String url = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		Integer window = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), Integer.class);

		try {
			theo.updateWindow(window, null, url, null, null);
		} catch (Exception e) {
			
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
