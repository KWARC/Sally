package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.interfaces.IAbstractMessageRunner;
import info.kwarc.sally.core.interfaces.SallyTask;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.SallyFrameChoice;

import com.google.inject.Inject;

@SallyTask(action="RunChoice")
public class RunChoice implements WorkItemHandler {
	Logger log; 
	CallbackManager callbacks;
	
	@Inject
	public RunChoice(CallbackManager callbacks) {
		log = LoggerFactory.getLogger(this.getClass());
		this.callbacks  = callbacks;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
			SallyFrameChoice m = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), SallyFrameChoice.class);
			IAbstractMessageRunner runner = callbacks.getCallback(m.getCallbackToken());
			if (runner != null) {
				runner.run(m);
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
