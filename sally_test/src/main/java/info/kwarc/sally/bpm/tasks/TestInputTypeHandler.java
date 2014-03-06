package info.kwarc.sally.bpm.tasks;

import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import org.junit.Assert;

public class TestInputTypeHandler implements WorkItemHandler {
	
	Class<?> inputType;
	Object output;
	
	public TestInputTypeHandler(Class<?> inputType) {
		this(inputType, null);
	}

	public TestInputTypeHandler(Class<?> inputType, Object output) {
		this.inputType = inputType;
		this.output = output;
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem);
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		Object result = workItem.getFirstTypedParameter(inputType);
		if (result == null) {
			Assert.fail("No input of type "+inputType+" was given to "+workItem);
		}
		manager.completeWorkItem(workItem);
	}
}
