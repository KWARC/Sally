package info.kwarc.sally.planetary.tasks;

import info.kwarc.sally.core.theo.CookieProvider;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.planetary.Planetary;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="GenerateOntologyBrowseURL")
public class GenerateOntologyBrowseURL implements WorkItemHandler {

	Logger log;
	Planetary planetary;
	CookieProvider cookieProvider;
	
	@Inject
	public GenerateOntologyBrowseURL(Planetary planetary, CookieProvider cookieProvider) {
		log = LoggerFactory.getLogger(getClass());
		this.planetary = planetary;
		this.cookieProvider = cookieProvider;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
			cookieProvider.setCookies(planetary.getSessionCookie());
			planetary.enable_sally("concept_sender");
			workItem.getResults().put("URLOutput", planetary.getPlanetaryRoot());
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
