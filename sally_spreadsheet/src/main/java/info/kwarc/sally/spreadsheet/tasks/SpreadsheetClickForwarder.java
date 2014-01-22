package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.IPositionProvider;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import java.util.Map;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexClick;
import sally.ScreenCoordinates;

import com.google.inject.Inject;

@SallyTask(action="SpreadsheetClickForwarder")
public class SpreadsheetClickForwarder implements WorkItemHandler {

	Logger log;
	ISallyWorkflowManager kb;
	IPositionProvider positionProvider;
	
	@Inject
	public SpreadsheetClickForwarder(ISallyWorkflowManager kb, IPositionProvider positionProvider) {
		log = LoggerFactory.getLogger(getClass());
		this.positionProvider = positionProvider;
		this.kb = kb;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		AlexClick msg = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), AlexClick.class);
		Map<String, Object> variables = HandlerUtils.getProcessVariables(kb.getProcessInstance(workItem.getProcessInstanceId()));
		
		SpreadsheetDocument doc = HandlerUtils.getFirstTypedParameter(variables, SpreadsheetDocument.class);
		try {
			if (msg == null)
				throw new Exception("No click to forward");
			if (doc == null)
				throw new Exception("No document available");
			String mmtURI = doc.getSemantics(msg.getRange());
			ScreenCoordinates screenCoordinates = msg.getPosition();
			positionProvider.setRecommendedCoordinates(new Coordinates(screenCoordinates.getX(), screenCoordinates.getY()));
			
			log.info("Forwarding click to som " + kb.propagateChildMessage(workItem.getProcessInstanceId(), "Message-onSelectionChanged", mmtURI)); 
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
