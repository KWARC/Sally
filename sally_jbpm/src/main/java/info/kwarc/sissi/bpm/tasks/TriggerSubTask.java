package info.kwarc.sissi.bpm.tasks;

import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.MessageForward;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sissi.bpm.SubtaskCallbackMap;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

@SallyTask(action="TriggerSubtask")
public class TriggerSubTask implements WorkItemHandler {

	Logger log;
	ISallyWorkflowManager kb;
	SubtaskCallbackMap subtaskCallbackMap;
	CallbackManager callbackManager;
	
	@Inject
	public TriggerSubTask(ISallyWorkflowManager kb, CallbackManager callbackManager, SubtaskCallbackMap subtaskCallbackMap) {
		log = LoggerFactory.getLogger(getClass());
		this.subtaskCallbackMap = subtaskCallbackMap;
		this.kb = kb;
		this.callbackManager = callbackManager;
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		MessageForward sw = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), MessageForward.class);

		try {
			if (sw == null)
				throw new Exception("No StartWorkflow Input");
			Long callback = subtaskCallbackMap.getWorkflowSubtask(sw.getFrom());
			log.info("Got msg from "+sw.getFrom()+" -> ");
			log.info("Need to notify callback -> "+callback);
			if (callback != null) {
				IMessageCallback runner = callbackManager.getCallback(callback);
				if (runner == null) {
					throw new Exception("Runner for callback "+callback +" is not defined");
				}
				if (!(sw.getData() instanceof AbstractMessage)) {
					throw new Exception("Event data is not an abstract message");
				}
				runner.onMessage((AbstractMessage)sw.getData());
			}
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
