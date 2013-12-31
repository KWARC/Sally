package info.kwarc.sally.bpm.tasks;

import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
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
		manager.completeWorkItem(workItem.getId(), null);
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		Object result = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), inputType);
		if (result == null) {
			Assert.fail("No input of type "+inputType+" was given to "+workItem);
		}
		manager.completeWorkItem(workItem.getId(), null);
	}
}
