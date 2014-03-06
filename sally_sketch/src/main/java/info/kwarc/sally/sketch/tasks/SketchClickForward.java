package info.kwarc.sally.sketch.tasks;

import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.IPositionProvider;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.core.workflow.WorkflowUtils;
import info.kwarc.sally.sketch.SketchDocument;

import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.ScreenCoordinates;
import sally.SketchSelect;

import com.google.inject.Inject;

@SallyTask(action="SketchClickForwarder")

public class SketchClickForward implements WorkItemHandler {

	Logger log;
	ISallyWorkflowManager kb;
	IPositionProvider positionProvider;
	
	@Inject
	public SketchClickForward(ISallyWorkflowManager kb, IPositionProvider positionProvider) {
		log = LoggerFactory.getLogger(getClass());
		this.positionProvider = positionProvider;
		this.kb = kb;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		SketchSelect msg = workItem.getFirstTypedParameter(SketchSelect.class);
		Map<String, Object> variables = workItem.getProcessVariables();
		
		SketchDocument doc = WorkflowUtils.getFirstTypedParameter(variables, SketchDocument.class);
		try {
			if (msg == null)
				throw new Exception("No click to forward");
			if (doc == null)
				throw new Exception("No document available");
			String mmtURI = doc.getSemantics(msg.getId());
			ScreenCoordinates screenCoordinates = msg.getPosition();
			positionProvider.setRecommendedCoordinates(new Coordinates(screenCoordinates.getX(), screenCoordinates.getY()));
			
			log.info("Forwarding click to som " + kb.propagateChildMessage(workItem.getProcessInstanceId(), "Message-onSelectionChanged", mmtURI)); 
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}

}
