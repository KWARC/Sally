package info.kwarc.sally.tasks;

import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="DynamicApplicability")
public class DynamicApplyHandler implements WorkItemHandler {
	SallyInteraction interaction;
	Logger log;
	ISallyWorkflowManager kb;
	
	@Inject
	public DynamicApplyHandler(SallyInteraction interaction, ISallyWorkflowManager kb) {
		this.interaction = interaction;
		log = LoggerFactory.getLogger(this.getClass());
		this.kb = kb;
	}

	public void abortWorkItem(WorkItem arg0, WorkItemManager arg1) {

	}

	public void executeWorkItem(WorkItem arg0, WorkItemManager arg1) {
		Object o = arg0.getFirstTypedParameter(Object.class);

		try {
			if (o==null) {
				throw new Exception("failed finding a parameter ending in 'Input'");
			}
			String output = (String) arg0.getParameters().get("outputType");
			if (output == null || output.length() == 0) {
				output = "java.lang.Object";
			}

			Class<?> c = Class.forName(output);

			interaction.getContext().setContextVar("processInstanceId", arg0.getProcessInstanceId());
			arg0.addResult("result", interaction.getPossibleInteractions(o, c));
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			arg1.completeWorkItem(arg0);
		}
	}	
}