package info.kwarc.sally.tasks;

import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.MessageForward;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import java.util.HashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

@SallyTask(action="ForwardToInterface")
public class ForwardToInterface implements WorkItemHandler {

	DocumentManager docMap;
	Logger log;
	ISallyWorkflowManager kb;

	@Inject
	public ForwardToInterface(DocumentManager docMap, ISallyWorkflowManager kb) {
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
		@SuppressWarnings("unchecked")
		HashMap<String, ProcessInstance> interfaceMap = (HashMap<String, ProcessInstance>) workItem.getFirstTypedParameter(HashMap.class);

		try {
			if (!(msg.getData() instanceof AbstractMessage)) {
				throw new Exception("Don't know how to forward objects of type "+msg.getData().getClass());
			}

			AbstractMessage absmsg = (AbstractMessage) msg.getData();
			String pkg = "Sally."+absmsg.getDescriptorForType().getFile().getPackage();
			if (!interfaceMap.containsKey(pkg)) {
				throw new Exception(String.format("Package %s does not match any implemented interface name.", pkg));
			}
			ProcessInstance pi = interfaceMap.get(pkg);
			pi.sendMessageOrForward(workItem.getProcessInstanceId(), absmsg);
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}
}
