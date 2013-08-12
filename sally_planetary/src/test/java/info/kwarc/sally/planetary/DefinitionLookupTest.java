package info.kwarc.sally.planetary;

import java.util.HashMap;

import org.junit.Assert;

import info.kwarc.sally.core.injectors.TheoFirstChoice;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.injection.TestableKnowledeBase;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;
import info.kwarc.sissi.bpm.tasks.TestCounterHandler;
import info.kwarc.sissi.bpm.tasks.TestInputTypeHandler;

import org.drools.KnowledgeBase;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItemManager;
import org.jbpm.process.instance.impl.demo.SystemOutWorkItemHandler;
import org.jbpm.test.JbpmJUnitTestCase;
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
				new TestableKnowledeBase(createKnowledgeSession(b)),
				new TheoFirstChoice()
				);
	}
	
	@Test
	public void testWorkflow() {
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);
		HashMap<String, TestCounterHandler> counters = HandlerUtils.registerCounterHandlers(kb, "theoWindowCreate", "theoWindowUpdate");


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
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);
		kb.registerWorkItemHandler("theoWindowCreate", new TestInputTypeHandler(String.class));
		kb.registerWorkItemHandler("theoWindowUpdate", new TestInputTypeHandler(CADAlexClick.class));

		ProcessInstance inst = kb.startProcess(null, "Sally.deflookup");
		inst.signalEvent("Message-input", "test.url");
		inst.signalEvent("Message-selectionChanged", CADAlexClick.newBuilder().buildPartial());
	}
}
