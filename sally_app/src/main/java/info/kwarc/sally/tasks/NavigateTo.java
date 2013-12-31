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

import sally.AlexRangeRequest;
import sally.CADNavigateTo;

import com.google.inject.Inject;

@SallyTask(action="navigateTo")
public class NavigateTo implements WorkItemHandler {

	Logger log;
	ISallyWorkflowManager kb;
	
	@Inject
	public NavigateTo(ISallyWorkflowManager kb) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		AlexRangeRequest rangeInfo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), AlexRangeRequest.class);
		CADNavigateTo  navigateTo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), CADNavigateTo.class);

		Long pid = workItem.getProcessInstanceId();
		Map<String, Object> vars = HandlerUtils.getProcessVariables(kb.getProcessInstance(pid));
		
		SpreadsheetDocument wd = HandlerUtils.getFirstTypedParameter(vars, SpreadsheetDocument.class);
		CADDocument cd = HandlerUtils.getFirstTypedParameter(vars, CADDocument.class);

		try {
			
			if (wd!=null && rangeInfo != null && wd.getFilePath().equals(rangeInfo.getFileName())) {
				wd.selectRange(rangeInfo);
			}
			
			if (cd!=null && navigateTo != null && cd.getFilePath().equals(navigateTo.getFileName())) {
				cd.selectRange(navigateTo);
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
