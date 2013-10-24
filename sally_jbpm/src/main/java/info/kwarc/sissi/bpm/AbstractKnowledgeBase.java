package info.kwarc.sissi.bpm;

import info.kwarc.sally.core.MessageForward;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItemHandler;

public abstract class AbstractKnowledgeBase implements ISallyWorkflowManager{

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
	
	@Override
	public Long getWorkflowParent(Long processInstanceID) {
		return childParentRelation.get(processInstanceID);
	}
	
	@Override
	public List<Long> getWorkflowChildren(Long processInstanceID) {
		return parentChildRelation.get(processInstanceID);
	}

	private boolean trySendMessage(Long fromProcessID, Long targetProcessID, String message_id, Object input) {
		ProcessInstance pi = getProcessInstance(targetProcessID);
		for (String evt : BPMNUtils.getCallableEvents(pi)) {
			if (evt.equals(message_id)) {
				pi.signalEvent(message_id, input);
				return true;
			}
			if (evt.equals("Message-onForward")) {
				pi.signalEvent("Message-onForward", new MessageForward(fromProcessID, message_id, input));
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
			if (trySendMessage(currentProcessInstanceID, top, message_id, input)) {
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
	public boolean propagateParentMessage(Long processInstanceID, String message_id, Object input) {
		if (processInstanceID == null)
			return false;
		// Make sure it doesn't send messages to itself ...
		Long parentInstanceID = childParentRelation.get(processInstanceID);
		while (parentInstanceID != null) {
			if (trySendMessage(processInstanceID, parentInstanceID, message_id, input)) {
				return true;
			}
			parentInstanceID = childParentRelation.get(parentInstanceID);
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
		ProcessInstance pi = getSession().createProcessInstance(processID, obj);

		addRelation(parentProcessInstanceID, pi.getId());
		
		getSession().startProcessInstance(pi.getId());
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
