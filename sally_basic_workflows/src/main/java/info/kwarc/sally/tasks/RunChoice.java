package info.kwarc.sally.tasks;

import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.SallyFrameChoice;

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
			SallyFrameChoice m = workItem.getFirstTypedParameter(SallyFrameChoice.class);
			IMessageCallback runner = callbacks.getCallback(m.getCallbackToken());
			if (runner != null) {
				runner.onMessage(m);
			}
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

}
