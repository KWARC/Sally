package info.kwarc.sally.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;

import sally.WhoAmI;
import sally.WhoAmI.EnvironmentType;

import com.google.inject.Inject;
import com.google.inject.name.Named;

@SallyTask(action="InitTheo")
public class InitTheo implements WorkItemHandler {
	Theo desktopTheo;
	
	@Inject
	public InitTheo(@Named("DesktopTheo") Theo desktopTheo) {
		this.desktopTheo = desktopTheo;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem.getId(), null);
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		WhoAmI alexInfo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), WhoAmI.class);
		try {
			if (alexInfo == null) {
				throw new Exception("Got no AlexInfo message");
			}
			if (alexInfo.getEnvironmentType() == EnvironmentType.Desktop) {
				workItem.getResults().put("TheoOutput", desktopTheo);				
			} else {
				throw new Exception("No Theo available for environment "+alexInfo.getEnvironmentType());
			}
		} catch (Exception e) {
			
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}
}
