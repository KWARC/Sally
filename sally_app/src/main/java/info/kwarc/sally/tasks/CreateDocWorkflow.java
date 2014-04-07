package info.kwarc.sally.tasks;

import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.core.workflow.WorkflowUtils;

import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.WhoAmI;

import com.google.inject.Inject;
import com.google.inject.name.Named;

@SallyTask(action="CreateDocWorkflow")
public class CreateDocWorkflow implements WorkItemHandler {

	SallyInteraction interaction;
	ISallyWorkflowManager kb;
	DocumentManager docManager;
	Logger log;
	Theo desktopTheo;
	
	@Inject
	public CreateDocWorkflow(SallyInteraction interaction, ISallyWorkflowManager kb, DocumentManager docMap, @Named("DesktopTheo") Theo desktopTheo) {
		this.desktopTheo = desktopTheo;
		this.interaction = interaction;
		this.kb = kb;
		this.docManager = docMap;
		this.log = LoggerFactory.getLogger(this.getClass());
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

			ProcessInstance pi = kb.prepareProcess(workItem.getProcessInstanceId(), "Sally.document_workflow");
			pi.setProcessVarialbe("AlexInfo", alexInfo);
			pi.setProcessVarialbe("NetworkSender", networkSender);
			DocumentInformation docInfo = new DocumentInformation(alexInfo.getFileName(), pi.getId());
			docInfo.setTheo(desktopTheo);
			docManager.addDocument(docInfo);
			kb.startProcess(pi);
			
		} catch  (Exception e) {
			e.printStackTrace();
		}  finally {
			manager.completeWorkItem(workItem);
		}

	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {

	}

}
