package info.kwarc.sally.tasks;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;
import info.kwarc.sissi.model.document.cad.CADDocument;

import java.util.Map;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="Switch_App")
public class SwitchApp implements WorkItemHandler {

	Logger log;
	ISallyKnowledgeBase kb;
	
	@Inject
	public SwitchApp(ISallyKnowledgeBase kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String fileName = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		Long pid = workItem.getProcessInstanceId();
		Map<String, Object> vars = HandlerUtils.getProcessVariables(kb.getProcessInstance(pid));
		
		WorksheetDocument wd = HandlerUtils.getFirstTypedParameter(vars, WorksheetDocument.class);
		CADDocument cd = HandlerUtils.getFirstTypedParameter(vars, CADDocument.class);

		try {
			if (fileName == null)
				throw new Exception("FileName in SwitchApp cannot be null");

			if (wd!=null && wd.getFilePath().equals(fileName)) {
				wd.switchToApp();
			}
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
