package info.kwarc.sissi.bpm.injection;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;

import com.google.inject.AbstractModule;
import com.google.inject.name.Names;

/**
 * This module makes sure that SallyActions as well as DynamicApplicability are 
 * executed by running the real implementations
 * @author cjucovschi
 *
 */
public class StubSallyActions extends AbstractModule {
	Logger log;

	static class StubItemHandler implements WorkItemHandler{

		@Override
		public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
			manager.completeWorkItem(workItem.getId(), null);
		}

		@Override
		public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
			manager.completeWorkItem(workItem.getId(), null);
		}
		
	}
	
	@Override
	protected void configure() {
		bind(WorkItemHandler.class).annotatedWith(Names.named("SallyTask")).to(StubItemHandler.class);
		bind(WorkItemHandler.class).annotatedWith(Names.named("DynamicApplicability")).to(StubItemHandler.class);
	}

}
