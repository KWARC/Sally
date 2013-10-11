package info.kwarc.sally.tasks;

import info.kwarc.sally.ProcessDocMappings;
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

@SallyTask(action="forwardToParent")
public class ForwardToParent implements WorkItemHandler {

	ProcessDocMappings docMap;
	Logger log;
	ISallyKnowledgeBase kb;

	@Inject
	public ForwardToParent(ProcessDocMappings docMap, ISallyKnowledgeBase kb) {
		this.docMap = docMap;
		log = LoggerFactory.getLogger(this.getClass());
		this.kb = kb;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		MessageForward msg = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), MessageForward.class);
		try {
			if (msg == null)
				throw new Exception("No MessageForward input given");
			Long processInstanceID = workItem.getProcessInstanceId();
			String msgType = msg.getType();
			Object data = msg.getData();
			kb.propagateParentMessage(processInstanceID, msgType, data);
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), null);
		}
	}
}
