package info.kwarc.sally.bpm.tasks;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

import java.util.HashMap;

public class TestHandlerUtils {
	public static HashMap<String, TestCounterHandler> registerCounterHandlers(ISallyWorkflowManager kb, String ...handlers) {
		HashMap<String, TestCounterHandler> result = new HashMap<String, TestCounterHandler>();
		for (String handler : handlers) {
			TestCounterHandler counterHandler = new TestCounterHandler();
			kb.registerWorkItemHandler(handler, counterHandler);
			result.put(handler, counterHandler);
		}
		return result;
	}
}
