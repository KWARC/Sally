package info.kwarc.sally.planetary;

import info.kwarc.sally.bpm.tasks.TestCounterHandler;
import info.kwarc.sally.bpm.tasks.TestHandlerUtils;
import info.kwarc.sally.bpm.tasks.TestInputTypeHandler;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sissi.bpm.injection.TestableKnowledeBase;

import java.util.HashMap;

import org.drools.KnowledgeBase;
import org.drools.runtime.process.ProcessInstance;
import org.jbpm.test.JbpmJUnitTestCase;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import sally.CADAlexClick;
import sally.CADSemanticData;

import com.google.inject.Guice;
import com.google.inject.Injector;

public class DefinitionLookupTest extends JbpmJUnitTestCase {
	Injector i;
	CADSemanticData alexData;

	@Before
	public void setup() throws Exception {
		KnowledgeBase b = createKnowledgeBaseGuvnor("Sally");
		i = Guice.createInjector(
				new TestableKnowledeBase(createKnowledgeSession(b))
				);
	}
	
	@Test
	public void testWorkflow() {
		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		HashMap<String, TestCounterHandler> counters = TestHandlerUtils.registerCounterHandlers(kb, "theoWindowCreate", "theoWindowUpdate");


		HashMap<String, Object>  input = new  HashMap<String, Object>();
		input.put("URLOutput", "testurl");

		ProcessInstance inst = kb.startProcess(null, "Sally.deflookup", input);
		inst.signalEvent("Message-input", "test.url");
		inst.signalEvent("Message-selectionChanged", null);

		Assert.assertEquals(1, counters.get("theoWindowCreate").getExecuted());
		Assert.assertEquals(1, counters.get("theoWindowUpdate").getExecuted());
	}
	
	@Test
	public void testInputs() {
		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		kb.registerWorkItemHandler("theoWindowCreate", new TestInputTypeHandler(String.class));
		kb.registerWorkItemHandler("theoWindowUpdate", new TestInputTypeHandler(CADAlexClick.class));

		ProcessInstance inst = kb.startProcess(null, "Sally.deflookup");
		inst.signalEvent("Message-input", "test.url");
		inst.signalEvent("Message-selectionChanged", CADAlexClick.newBuilder().buildPartial());
	}
}
