package info.kwarc.sally.tasks;

import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.WhoAmI;
import Sally.WhoAmI.EnvironmentType;

import com.google.inject.Inject;
import com.google.inject.name.Named;

@SallyTask(action="InitTheo")
public class InitTheo implements WorkItemHandler {
	Theo desktopTheo, webTheo;
	Logger log;
	
	@Inject
	public InitTheo(@Named("DesktopTheo") Theo desktopTheo, @Named("WebTheo") Theo webTheo) {
		log = LoggerFactory.getLogger(getClass());
		this.desktopTheo = desktopTheo;
		this.webTheo = webTheo;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem);
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		WhoAmI alexInfo = workItem.getFirstTypedParameter(WhoAmI.class);
		try {
			if (alexInfo == null) {
				throw new Exception("Got no AlexInfo message");
			}
			log.info(alexInfo.toString());

			if (alexInfo.getEnvironmentType() == EnvironmentType.Desktop) {
				workItem.addResult("TheoOutput", desktopTheo);				
			} else if (alexInfo.getEnvironmentType() == EnvironmentType.Web) {
				workItem.addResult("TheoOutput", webTheo);				
			}
			else {
				throw new Exception("No Theo available for environment "+alexInfo.getEnvironmentType());
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			manager.completeWorkItem(workItem);
		}
	}
}
