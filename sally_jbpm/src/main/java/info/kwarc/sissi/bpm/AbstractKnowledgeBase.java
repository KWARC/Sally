package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItemHandler;

public abstract class AbstractKnowledgeBase implements ISallyKnowledgeBase{

	HashMap<Long, Long> childParentRelation;
	HashMap<Long, Stack<Long>> parentChildRelation;

	protected abstract StatefulKnowledgeSession getSession();

	@Override
	public void signal_global_event(String signal_ref, Object data) {
		getSession().signalEvent(signal_ref, data);
	}

	public AbstractKnowledgeBase() {
		childParentRelation = new HashMap<Long, Long>();
		parentChildRelation = new HashMap<Long, Stack<Long>>();
	}

	private boolean trySendMessage(Long processID, String message_id, Object input) {
		ProcessInstance pi = getProcessInstance(processID);
		for (String evt : BPMNUtils.getCallableEvents(pi)) {
			if (evt.equals(message_id)) {
				pi.signalEvent(message_id, input);
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean propagateChildMessage(Long currentProcessInstanceID,
			String message_id, Object input) {

		Stack<Long> children = parentChildRelation.get(currentProcessInstanceID);

		Stack<Long> removed = new Stack<Long>();
		if (children == null) 
			return false;

		while (!children.empty()) {
			Long top = children.pop();
			if (trySendMessage(top, message_id, input)) {
				children.addAll(removed);
				children.add(top); // making sure that the last object remains on top
				return true;
			}
			removed.add(top);
		}
		children.addAll(removed);		
		return false;
	}

	@Override
	public boolean propagateParentMessage(Long currentProcessInstanceID, String message_id, Object input) {
		while (currentProcessInstanceID != null) {
			if (trySendMessage(currentProcessInstanceID, message_id, input)) {
				return true;
			}
			currentProcessInstanceID = childParentRelation.get(currentProcessInstanceID);
		}
		return false;
	}

	private void addRelation(Long parent, Long child) {
		if (parent == null || child == null)
			return;

		childParentRelation.put(child, parent);
		Stack<Long> children = parentChildRelation.get(parent);
		if (children == null) {
			children = new Stack<Long>();
			children.add(child);
			parentChildRelation.put(parent, children);
		} else {
			children.add(child);
		}
	}

	public ProcessInstance startProcess(Long parentProcessInstanceID,
			String processID) {

		ProcessInstance pi =getSession().startProcess(processID);

		addRelation(parentProcessInstanceID, pi.getId());

		return pi;
	}

	@Override
	public ProcessInstance startProcess(Long parentProcessInstanceID,
			String processID, Map<String, Object> obj) {
		ProcessInstance pi =getSession().startProcess(processID, obj);

		addRelation(parentProcessInstanceID, pi.getId());
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
