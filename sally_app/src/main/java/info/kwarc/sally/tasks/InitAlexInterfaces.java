package info.kwarc.sally.tasks;

import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.core.workflow.WorkflowUtils;
import info.kwarc.sally.html.HTMLFactory;
import info.kwarc.sally.sketch.SketchFactory;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;
import info.kwarc.sissi.model.document.cad.interfaces.CADFactory;

import java.util.HashMap;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.WhoAmI;

import com.google.inject.Inject;

@SallyTask(action="InitAlexInterfaces")
public class InitAlexInterfaces implements WorkItemHandler {

	CADFactory cadFactory;
	WorksheetFactory spreadsheetFactory;
	SketchFactory sketchFactory;
	HTMLFactory htmlFactory;

	SallyInteraction interaction;
	ISallyWorkflowManager kb;
	DocumentManager docManager;
	Logger log;

	@Inject
	public InitAlexInterfaces(SallyInteraction interaction, ISallyWorkflowManager kb, DocumentManager docMap) {
		this.interaction = interaction;
		this.kb = kb;
		this.docManager = docMap;
		this.log = LoggerFactory.getLogger(this.getClass());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		WhoAmI alexInfo = workItem.getFirstTypedParameter(WhoAmI.class);

		Map<String, Object> variable = kb.getProcessInstance(workItem.getProcessInstanceId()).getProcessVariables();
		INetworkSender networkSender = WorkflowUtils.safeGet(variable, "NetworkSender", INetworkSender.class);		
		try{
			if (networkSender == null)
				throw new Exception("No network sender available.");

			if (alexInfo == null)
				throw new Exception("No WhoAmI object passed to document creation. Aborting document creation.");

			HashMap<String, ProcessInstance> interfaceMap = new HashMap<String, ProcessInstance>();
			Map<String, Object> params = new HashMap<String, Object>();

			for (String iface: alexInfo.getInterfacesList()) {
				try {
					ProcessInstance instance = kb.startProcess(workItem.getProcessInstanceId(), iface, params);
					interfaceMap.put(iface, instance);
				} catch (Exception e) {
				} 
			}
			workItem.addResult("InterfaceMapOutput", interfaceMap);
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}
	}
}
