package info.kwarc.sissi.bpm.implementation;


import info.kwarc.sally.core.workflow.MessageForward;
import info.kwarc.sally.core.workflow.ProcessInstance;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.drools.runtime.process.NodeInstance;
import org.jbpm.ruleflow.instance.RuleFlowProcessInstance;
import org.jbpm.workflow.instance.node.CompositeNodeInstance;
import org.jbpm.workflow.instance.node.EventNodeInstance;

import com.google.protobuf.AbstractMessage;

public class JBPMProcessInstance  implements ProcessInstance {
	org.drools.runtime.process.ProcessInstance pi;
	
	public JBPMProcessInstance(org.drools.runtime.process.ProcessInstance pi) {
		this.pi = pi;
	}
	
	@Override
	public Map<String, Object> getProcessVariables() {
		if (pi instanceof RuleFlowProcessInstance) {
			return ((RuleFlowProcessInstance) pi).getVariables();
		}
		return new HashMap<String, Object>();
	}

	@Override
	public void setProcessVarialbe(String var, Object value) {
		if (pi instanceof RuleFlowProcessInstance) {
			((RuleFlowProcessInstance) pi).setVariable(var, value);
		}
	}

	public Collection<NodeInstance> getNodeInstances() {
		ArrayList<NodeInstance> result = new ArrayList<NodeInstance>();
		if (pi instanceof RuleFlowProcessInstance) {
			RuleFlowProcessInstance flow = ((RuleFlowProcessInstance) pi);
			for (NodeInstance nodeInst : flow.getNodeInstances()) {
				if (nodeInst instanceof CompositeNodeInstance) {
					CompositeNodeInstance embedded = ((CompositeNodeInstance) nodeInst);
					for (NodeInstance nodeInst2 : embedded.getNodeInstances()) {
						result.add(nodeInst2);
					}
				} else {
					result.add(nodeInst);
				}
			}
		}
		return result;
	}

	public Collection<String> getCallableEvents() {
		ArrayList<String> result = new ArrayList<String>();
		for (String s : pi.getEventTypes()) {
			result.add(s);
		}
		
		for (NodeInstance inst : getNodeInstances()) {
			if (inst instanceof EventNodeInstance) {
				result.add(((EventNodeInstance) inst).getEventNode().getType());
			}
		}
		return result;
	}

	@Override
	public void sendMessageOrForward(Long from, String eventType, Object eventData) {
		Boolean forwardExists = false;
		for (String events : getCallableEvents()) {
			if (events.equals(eventType)) {
				pi.signalEvent(eventType, eventData);
				return;
			}
			if (events.equals("Message-onForward")) {
				forwardExists = true;
			}
		}
		if (forwardExists) {
			pi.signalEvent("Message-onForward", new MessageForward(from, eventType, eventData));
		} else
		{
			for (NodeInstance ni : getNodeInstances()) {
				System.out.println(ni.getNodeName());
			}
			for (String events : getCallableEvents()) {
				System.out.println(events);
			}			
		}		
	}

	@Override
	public void sendMessageOrForward(Long from, AbstractMessage msg) {
		sendMessageOrForward(from, "Message-"+msg.getClass().getSimpleName(), msg);		
	}

	@Override
	public void signalEvent(String msg, Object data) {
		pi.signalEvent(msg, data);
	}

	@Override
	public Long getId() {
		return pi.getId();
	}
	
}
