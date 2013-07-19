package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.injection.Configuration;
import info.kwarc.sissi.bpm.injection.StubSallyActions;
import info.kwarc.sissi.bpm.injection.TestableKnowledeBase;

import org.drools.runtime.process.ProcessInstance;
import org.jbpm.test.JbpmJUnitTestCase;
import org.junit.Before;
import org.junit.Test;

import com.google.inject.Guice;
import com.google.inject.Injector;

public class ConnectionManagerTest extends JbpmJUnitTestCase {

	Injector i;

	@Before
	public void setup() {
		i = Guice.createInjector(
				new Configuration(),
				new TestableKnowledeBase(createKnowledgeSession("connect.bpmn")), 
				new StubSallyActions()
				);
	}

	@Test
	public void testOneConnectAndDisconnect() {
		
		ConnectionManager c = i.getInstance(ConnectionManager.class);
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);

		c.newClient("client1");
		c.newMessage("client1", "sally.WhoAmI", null);
		c.newMessage("client1", "onDisconnect", null);

		ProcessInstance processInstance = c.getState("client1");
		assertProcessInstanceCompleted(processInstance.getId(), kb.getKnowledgeSession());
		assertNodeTriggered(processInstance.getId(), "StartProcess", "sally.WhoAmI", "End");
	}

	@Test
	public void testOneConnectOneSemanticDataAndDisconnect() {
		
		ConnectionManager c = i.getInstance(ConnectionManager.class);
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);

		c.newClient("client1");
		c.newMessage("client1", "sally.WhoAmI", null);
		c.newMessage("client1", "sally.SemanticData", null);
		c.newMessage("client1", "onDisconnect", null);

		ProcessInstance processInstance = c.getState("client1");
		assertProcessInstanceCompleted(processInstance.getId(), kb.getKnowledgeSession());
		assertNodeTriggered(processInstance.getId(), "StartProcess", "sally.WhoAmI", "SemanticData", "CreateDocument", "End");
	}
	
}