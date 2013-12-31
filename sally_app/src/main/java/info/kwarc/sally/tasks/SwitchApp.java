package info.kwarc.sally.tasks;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
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
	ISallyWorkflowManager kb;
	
	@Inject
	public SwitchApp(ISallyWorkflowManager kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		String fileName = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), String.class);
		Long pid = workItem.getProcessInstanceId();
		Map<String, Object> vars = HandlerUtils.getProcessVariables(kb.getProcessInstance(pid));
		
		SpreadsheetDocument wd = HandlerUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
		CADDocument cd = HandlerUtils.getFirstTypedParameter(vars, CADDocument.class);

		try {
			if (fileName == null)
				throw new Exception("FileName in SwitchApp cannot be null");

			if (wd!=null && wd.getFilePath().equals(fileName)) {
				wd.switchToApp();
			}
			if (cd!=null && cd.getFilePath().equals(fileName)) {
				cd.switchToApp();
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
