package info.kwarc.sally.tasks;

import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import XSelectionProvider.OnSelect;

import com.google.inject.Inject;

@SallyTask(action="SelectionForwarder")
public class SelectForward implements WorkItemHandler {

	DocumentManager docMap;
	Logger log;
	ISallyWorkflowManager kb;
	
	@Inject
	public SelectForward(DocumentManager docMap, ISallyWorkflowManager kb) {
		this.docMap = docMap;
		log = LoggerFactory.getLogger(this.getClass());
		this.kb = kb;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		OnSelect msg = workItem.getFirstTypedParameter(OnSelect.class);

		try {
			log.info("Forwarding click to som " + kb.propagateChildMessage(workItem.getProcessInstanceId(), "Message-"+msg.getClass().getName(), msg)); 
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}
}
