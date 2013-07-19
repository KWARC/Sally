package info.kwarc.sissi.bpm.handlers;

import info.kwarc.sally.core.SallyAction;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.name.Names;

public class SallyTaskHandler implements WorkItemHandler  {
	
	Injector injector;
	
	@Inject
	public SallyTaskHandler(Injector injector) {
		this.injector = injector;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String actionId = (String) workItem.getParameter("actionId");

		try {
			SallyAction a = injector.getInstance(Key.get(SallyAction.class, Names.named(actionId)));
			a.run(workItem.getParameters());
		} catch (Exception e){
			manager.abortWorkItem(workItem.getId());
			return;
		}
		manager.completeWorkItem(workItem.getId(), null);
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

}
