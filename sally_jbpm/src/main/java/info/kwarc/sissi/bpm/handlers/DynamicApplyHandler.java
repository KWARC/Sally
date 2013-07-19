package info.kwarc.sissi.bpm.handlers;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

public class DynamicApplyHandler implements WorkItemHandler {

	public void abortWorkItem(WorkItem arg0, WorkItemManager arg1) {
		
	}

	public void executeWorkItem(WorkItem arg0, WorkItemManager arg1) {
		System.out.println(arg0.getName());
		arg1.completeWorkItem(arg0.getId(), null);
	}
	
}
