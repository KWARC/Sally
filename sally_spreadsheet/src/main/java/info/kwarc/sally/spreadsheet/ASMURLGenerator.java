package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.interfaces.SallyTask;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
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
		workItem.getResults().put("URLOutput", "http://localhost:8181/sally/asmeditor?pid="+workItem.getProcessInstanceId());
		manager.completeWorkItem(workItem.getId(), workItem.getResults());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
