package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sissi.bpm.SubtaskCallbackMap;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;

@SallyTask(action="StartSubTask")
public class StartSubTask implements WorkItemHandler {

	Logger log;
	ISallyWorkflowManager kb;
	SubtaskCallbackMap subtaskMap;
	
	@Inject
	public StartSubTask(ISallyWorkflowManager kb, SubtaskCallbackMap subtaskMap) {
		log = LoggerFactory.getLogger(getClass());
		this.kb = kb;
		this.subtaskMap = subtaskMap;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		sally.StartSubTask sw = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), sally.StartSubTask.class);
		
		try {
			if (sw == null)
				throw new Exception("No StartWorkflow Input");
			ProcessInstance pi = kb.startProcess(workItem.getProcessInstanceId(), sw.getWorkflowID());
			subtaskMap.registerCallbackForWorkflow(pi.getId(), sw.getCallbackToken());
			log.info("Assigning workflow "+pi.getId()+ " to callback "+sw.getCallbackToken());
			workItem.getResults().put("workflowID", pi.getId());
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
