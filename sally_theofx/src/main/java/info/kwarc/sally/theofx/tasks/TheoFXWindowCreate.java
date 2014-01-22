package info.kwarc.sally.theofx.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.theo.ScreenCoordinatesProvider;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="theoWindowCreate")
public class TheoFXWindowCreate implements WorkItemHandler {
	ScreenCoordinatesProvider screenCoords;
	Logger log;
	DocumentManager docManager;
	
	@Inject
	public TheoFXWindowCreate(ScreenCoordinatesProvider screenCoords, DocumentManager docManager) {
		this.screenCoords = screenCoords;
		this.docManager = docManager;
		log = LoggerFactory.getLogger(this.getClass());
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String url = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		try {
			if (url == null) 
				throw new Exception("No URL given");
			DocumentInformation docInfo = docManager.getDocumentInformation(workItem);
			if (docInfo == null)
				throw new Exception("No document associated with this workflow");
			Theo theo = docInfo.getTheo();
			int theoOutput = theo.openWindow(docInfo, workItem.getProcessInstanceId(), "", url, 700, 600);
			workItem.getResults().put("wndIDOutput", theoOutput);
		} catch (Exception e) {
			log.error(e.getMessage());
			e.printStackTrace();
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}

	@Override
	public void abortWorkItem(WorkItem arg0, WorkItemManager arg1) {
		// TODO Auto-generated method stub
		
	}

}
