package info.kwarc.sissi.bpm;

import info.kwarc.sally.core.MessageForward;

import java.util.ArrayList;
import java.util.Collection;

import org.drools.runtime.StatefulKnowledgeSession;
import org.drools.runtime.process.NodeInstance;
import org.drools.runtime.process.ProcessInstance;
import org.jbpm.ruleflow.instance.RuleFlowProcessInstance;
import org.jbpm.workflow.instance.node.CompositeNodeInstance;
import org.jbpm.workflow.instance.node.EventNodeInstance;
import org.slf4j.LoggerFactory;

public class BPMNUtils {
	public static void sendMessageOrForward(ProcessInstance processInstance, String eventType, Object eventData) {
		Boolean forwardExists = false;
		for (String events : BPMNUtils.getCallableEvents(processInstance)) {
			if (events.equals(eventType)) {
				processInstance.signalEvent(eventType, eventData);
				return;
			}
			if (events.equals("Message-onForward")) {
				forwardExists = true;
			}
		}
		if (forwardExists) {
			processInstance.signalEvent("Message-onForward", new MessageForward(eventType, eventData));
		} else
		{
			LoggerFactory.getLogger(BPMNUtils.class).warn("Event "+eventType+" is not handled and no forwarding exists. And hence will be ignored.");
		}
	}

	public static void showStatus(StatefulKnowledgeSession session) {
		for (ProcessInstance pi : session.getProcessInstances()) {
			System.out.println("Process instance "+pi.getId()+" ("+pi.getProcessName()+")");
			for (NodeInstance instance : getNodeInstances(pi)) {
				System.out.println(instance.getNodeName());
			}
		}		
	}

	public static Collection<NodeInstance> getNodeInstances(ProcessInstance pi) {
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


	public static Collection<String> getCallableEvents(ProcessInstance pi) {
		ArrayList<String> result = new ArrayList<String>();
		for (String s : pi.getEventTypes()) {
			result.add(s);
		}
		
		for (NodeInstance inst : getNodeInstances(pi)) {
			if (inst instanceof EventNodeInstance) {
				result.add(((EventNodeInstance) inst).getEventNode().getType());
			}
		}
		return result;
	}
}
