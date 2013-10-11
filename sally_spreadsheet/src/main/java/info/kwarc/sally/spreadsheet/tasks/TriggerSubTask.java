package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.MessageForward;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="TriggerSubtask")
public class TriggerSubTask implements WorkItemHandler {

	Logger log;
	ISallyKnowledgeBase kb;

	@Inject
	public TriggerSubTask(ISallyKnowledgeBase kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		MessageForward sw = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), MessageForward.class);

		try {
			if (sw == null)
				throw new Exception("No StartWorkflow Input");
			log.info("Got msg from "+sw.getFrom()+" -> ");
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}


}
