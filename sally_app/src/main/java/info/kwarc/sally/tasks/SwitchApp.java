package info.kwarc.sally.tasks;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.core.workflow.WorkflowUtils;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sissi.model.document.cad.CADDocument;

import java.util.Map;

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
		String fileName = workItem.getFirstTypedParameter(String.class);
		Long pid = workItem.getProcessInstanceId();
		Map<String, Object> vars = workItem.getProcessVariables();
		
		SpreadsheetDocument wd = WorkflowUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
		CADDocument cd = WorkflowUtils.getFirstTypedParameter(vars, CADDocument.class);

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
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}
	
}
