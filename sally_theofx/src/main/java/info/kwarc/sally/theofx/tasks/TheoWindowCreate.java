package info.kwarc.sally.theofx.tasks;

import info.kwarc.sally.core.ScreenCoordinatesProvider;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="theoWindowCreate")
public class TheoWindowCreate implements WorkItemHandler {
	ScreenCoordinatesProvider screenCoords;
	Theo theo;
	Logger log;
	
	@Inject
	public TheoWindowCreate(ScreenCoordinatesProvider screenCoords, Theo theo) {
		this.screenCoords = screenCoords;
		this.theo = theo;
		log = LoggerFactory.getLogger(this.getClass());
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String url = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		try {
			if (url == null) 
				throw new Exception("No URL given");
			int theoOutput = theo.openWindow(workItem.getProcessInstanceId(), "", url, 700, 600);
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
