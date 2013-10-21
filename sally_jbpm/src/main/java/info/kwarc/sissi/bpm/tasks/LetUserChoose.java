package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.theo.Theo;

import java.util.List;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
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
		List<SallyMenuItem> choices= HandlerUtils.getFirstTypedParameter(workItem.getParameters(), List.class);
		try {
			if (choices==null) {
				throw new Exception("failed finding a parameter ending in 'Input'");
			}
			DocumentInformation documentInfo = docManager.getDocumentInformation(workItem);
			Theo theo = documentInfo.getTheo();
			theo.letUserChoose(documentInfo.getNetworkSender(), workItem.getProcessInstanceId(), choices);
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
