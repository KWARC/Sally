package info.kwarc.sally.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.MessageForward;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally_comm.MessageUtils;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

@SallyTask(action="forwardToDoc")
public class ForwardToDoc implements WorkItemHandler {

	DocumentManager docMap;
	Logger log;
	ISallyWorkflowManager kb;

	@Inject
	public ForwardToDoc(DocumentManager docMap, ISallyWorkflowManager kb) {
		this.docMap = docMap;
		log = LoggerFactory.getLogger(this.getClass());
		this.kb = kb;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		MessageForward msg = workItem.getFirstTypedParameter(MessageForward.class);
		try {
			if (!(msg.getData() instanceof AbstractMessage)) {
				throw new Exception("Don't know how to forward objects of type "+msg.getData().getClass());
			}

			AbstractMessage absmsg = (AbstractMessage) msg.getData();
			String fileName = MessageUtils.getFileNameFromMessage(absmsg);
			if (fileName  == null) {
				throw new Exception("No file name could be extracted from the forwarding message. Skipping.");
			}
			
			DocumentInformation docInfo = docMap.getDocumentInformation(fileName);
			if (docInfo == null)
				throw new Exception("No document corresponds to file name "+fileName);
			
			Long pforward = docInfo.getDocumentWorkflowID();
			if (pforward == null)
				throw new Exception("No process ID corresponds to file name "+fileName);

			System.out.println("Forwarded to process id="+pforward);
			kb.getProcessInstance(pforward).sendMessageOrForward(workItem.getProcessInstanceId(), msg.getType(), msg.getData());
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}
}
