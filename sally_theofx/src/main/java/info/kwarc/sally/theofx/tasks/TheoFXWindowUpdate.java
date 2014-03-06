package info.kwarc.sally.theofx.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="theoWindowUpdate")
public class TheoFXWindowUpdate implements WorkItemHandler{

	Logger log;
	DocumentManager docManager;
	
	@Inject
	public TheoFXWindowUpdate(DocumentManager docManager) {
		log = LoggerFactory.getLogger(getClass());
		this.docManager  =docManager;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String url = workItem.getFirstTypedParameter(String.class);
		Integer window = workItem.getFirstTypedParameter(Integer.class);
		DocumentInformation docInfo = docManager.getDocumentInformation(workItem);
		
		try {
			if (docInfo == null)
				throw new Exception("No document associated with this workflow");
			Theo theo = docInfo.getTheo();

			theo.updateWindow(docInfo, window, null, url, null, null);
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
