package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@SallyTask(action="ASMGenerateURL")
public class ASMURLGenerator implements WorkItemHandler {

	Logger log;
	
	public ASMURLGenerator() {
		log = LoggerFactory.getLogger(getClass());
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		log.info("Executing generate");
		workItem.addResult("URLOutput", "http://localhost:8181/sally/asmeditor?pid="+workItem.getProcessInstanceId());
		manager.completeWorkItem(workItem);
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
