package info.kwarc.sally.tasks;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.MessageForward;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.BPMNUtils;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
		MessageForward msg = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), MessageForward.class);
		try {
			if (!(msg.getData() instanceof AbstractMessage)) {
				throw new Exception("Don't know how to forward objects of type "+msg.getData().getClass());
			}

			AbstractMessage absmsg = (AbstractMessage) msg.getData();
			String fileName = HandlerUtils.getFileNameFromMessage(absmsg);
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
			BPMNUtils.sendMessageOrForward(workItem.getProcessInstanceId(), kb.getProcessInstance(pforward), msg.getType(), msg.getData());
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), null);
		}
	}
}
