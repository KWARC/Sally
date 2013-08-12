package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.util.HashMap;
import java.util.Map;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItemHandler;

public abstract class AbstractKnowledgeBase implements ISallyKnowledgeBase{

	HashMap<Long, Long> parentRelation;

	protected abstract StatefulKnowledgeSession getSession();

	@Override
	public boolean propagateParentMessage(Long currentProcessInstanceID, String message_id, Object input) {
		while (currentProcessInstanceID != null) {
			ProcessInstance pi = getProcessInstance(currentProcessInstanceID);
			for (String evt : BPMNUtils.getCallableEvents(pi)) {
				if (evt.equals(message_id)) {
					pi.signalEvent(message_id, input);
					return true;
				}
			}			
			currentProcessInstanceID = parentRelation.get(currentProcessInstanceID);
		}
		return false;
	}

	public AbstractKnowledgeBase() {
		parentRelation = new HashMap<Long, Long>();
	}

	public ProcessInstance startProcess(Long parentProcessInstanceID,
			String processID) {

		ProcessInstance pi =getSession().startProcess(processID);

		if (parentProcessInstanceID != null && pi != null) {
			parentRelation.put(pi.getId(), parentProcessInstanceID);
		}
		return pi;
	}

	@Override
	public ProcessInstance startProcess(Long parentProcessInstanceID,
			String processID, Map<String, Object> obj) {
		ProcessInstance pi =getSession().startProcess(processID, obj);

		if (parentProcessInstanceID != null && pi != null) {
			parentRelation.put(pi.getId(), parentProcessInstanceID);
		}
		return pi;
	}

	@Override
	public ProcessInstance getProcessInstance(Long processinstanceID) {
		if (processinstanceID == null)
			return null;

		return getSession().getProcessInstance(processinstanceID);
	}

	@Override
	public void registerWorkItemHandler(String Name, WorkItemHandler handler) {
		getSession().getWorkItemManager().registerWorkItemHandler(Name, handler);
	}

}
