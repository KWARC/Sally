package info.kwarc.sally.tasks;

import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="RemoveCallback")
public class RemoveCallback  implements WorkItemHandler {
	Logger log;
	DocumentManager docManager;
	CallbackManager callbacks;
	
	@Inject
	public RemoveCallback(DocumentManager docManager, CallbackManager callbacks) {
		this.docManager = docManager;
		log = LoggerFactory.getLogger(this.getClass());
		this.callbacks = callbacks;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
/*			workItem.addResult("CallbackOutput", callbacks.(new IMessageCallback() {
				
				@Override
				public void onMessage(AbstractMessage msg) {
					log.info("got "+msg);
				}
			}));*/
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
