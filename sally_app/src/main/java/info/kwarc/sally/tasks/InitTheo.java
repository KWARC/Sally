package info.kwarc.sally.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.WhoAmI;
import sally.WhoAmI.EnvironmentType;

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
		manager.completeWorkItem(workItem.getId(), null);
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		WhoAmI alexInfo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), WhoAmI.class);
		try {
			if (alexInfo == null) {
				throw new Exception("Got no AlexInfo message");
			}
			log.info(alexInfo.toString());

			if (alexInfo.getEnvironmentType() == EnvironmentType.Desktop) {
				workItem.getResults().put("TheoOutput", desktopTheo);				
			} else if (alexInfo.getEnvironmentType() == EnvironmentType.Web) {
				workItem.getResults().put("TheoOutput", webTheo);				
			}
			else {
				throw new Exception("No Theo available for environment "+alexInfo.getEnvironmentType());
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}
}
