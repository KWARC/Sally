package info.kwarc.sally.tasks;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="LetUserChoose")
public class LetUserChoose implements WorkItemHandler {
	Logger log;
	DocumentManager docManager;
	CallbackManager callbacks;
	
	@Inject
	public LetUserChoose(DocumentManager docManager, CallbackManager callbacks) {
		this.docManager = docManager;
		log = LoggerFactory.getLogger(this.getClass());
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		List<SallyMenuItem> choices= (List<SallyMenuItem>) workItem.getFirstTypedParameter(List.class);
		try {
			if (choices==null) {
				throw new Exception("failed finding a parameter ending in 'Input'");
			}
			DocumentInformation documentInfo = docManager.getDocumentInformation(workItem);
			Theo theo = documentInfo.getTheo();
			theo.letUserChoose(documentInfo, choices);
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
