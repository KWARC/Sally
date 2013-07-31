package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.interfaces.Theo;

import java.util.List;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="LetUserChoose")
public class LetUserChoose implements WorkItemHandler {
	Theo theo;
	Logger log;
	
	@Inject
	public LetUserChoose(Theo theo) {
		this.theo = theo;
		log = LoggerFactory.getLogger(this.getClass());
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		List<SallyMenuItem> choices= HandlerUtils.getFirstTypedParameter(workItem.getParameters(), List.class);
		try {
			if (choices==null) {
				throw new Exception("failed finding a parameter ending in 'Input'");
			}
			SallyMenuItem item = theo.letUserChoose(choices);
			workItem.getResults().put("result", item);
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
