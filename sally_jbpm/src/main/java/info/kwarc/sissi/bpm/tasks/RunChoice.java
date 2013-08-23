package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@SallyTask(action="RunChoice")
public class RunChoice implements WorkItemHandler {
	Logger log; 
	
	public RunChoice() {
		log = LoggerFactory.getLogger(this.getClass());
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
	 		SallyMenuItem m = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), SallyMenuItem.class);
			if (m != null) {
				m.run();
			}
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

}
