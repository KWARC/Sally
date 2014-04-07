package info.kwarc.sally.tasks;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="DynamicApplicability")
public class DynamicApplyHandler implements WorkItemHandler {
	Logger log;
	ISallyWorkflowManager kb;
	DocumentManager docMan;
	
	@Inject
	public DynamicApplyHandler(SallyInteraction interaction, ISallyWorkflowManager kb, DocumentManager docMan) {
		this.docMan  = docMan;
		log = LoggerFactory.getLogger(this.getClass());
		this.kb = kb;
	}

	public void abortWorkItem(WorkItem arg0, WorkItemManager arg1) {

	}

	public void executeWorkItem(WorkItem arg0, WorkItemManager arg1) {
		Object o = arg0.getFirstTypedParameter(Object.class);

		try {
			SallyInteraction interaction = docMan.getDocumentInformation(arg0).getInteraction();
			if (o==null) {
				throw new Exception("failed finding a parameter ending in 'Input'");
			}
			if (arg0.getParameters().containsKey("CallBack")) {
				interaction.getContext().setContextVar("CallbackID", arg0.getParameters().get("CallBack"));
			}
			String output = (String) arg0.getParameters().get("outputType");
			if (output == null || output.length() == 0) {
				output = "java.lang.Object";
			}
			SallyMenuItem q;
			Class<?> c = Class.forName(output);

			interaction.getContext().setContextVar("processInstanceId", arg0.getProcessInstanceId());
			List res = interaction.getPossibleInteractions(o, c);
			arg0.addResult("result", res);
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			arg1.completeWorkItem(arg0);
		}
	}	
}