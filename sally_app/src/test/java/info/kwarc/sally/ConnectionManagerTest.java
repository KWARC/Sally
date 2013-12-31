package info.kwarc.sally;

import info.kwarc.sally.bpm.tasks.TestCounterHandler;
import info.kwarc.sally.core.net.IConnectionManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.injection.Configuration;
import info.kwarc.sally.networking.ConnectionManager;
import info.kwarc.sally.networking.interfaces.MockNetworkSender;
import info.kwarc.sissi.bpm.injection.TestableKnowledeBase;

import org.drools.KnowledgeBase;
import org.drools.runtime.process.ProcessInstance;
import org.jbpm.test.JbpmJUnitTestCase;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import com.google.inject.Guice;
import com.google.inject.Injector;

public class ConnectionManagerTest extends JbpmJUnitTestCase {

	Injector i;

	@Before
	public void setup() throws Exception {
		KnowledgeBase b = createKnowledgeBaseGuvnor("Sally");
		i = Guice.createInjector(
				new Configuration(),
				new TestableKnowledeBase(createKnowledgeSession(b)) 
				//new ProductionSallyActions()
				);
	}

	@Test
	public void testSimpleOneUser() {
		ConnectionManager c = i.getInstance(ConnectionManager.class);
		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		
		TestCounterHandler cntInit = new TestCounterHandler();
		TestCounterHandler cntCreateDoc = new TestCounterHandler();
		
		kb.registerWorkItemHandler("InitTheo", cntInit);
		kb.registerWorkItemHandler("CreateDoc", cntCreateDoc);
		
		c.newClient("user", new MockNetworkSender());
		c.newMessage("user", "Message-WhoAmI", "Spreadsheet");
		c.newMessage("user", "Message-AlexData", "a.xls");
		c.newMessage("user", "Message-AlexData", "b.xls");
		c.newMessage("user", "Message-Disconnect", null);
		
		ProcessInstance processInstance = c.getState("user");
		Assert.assertNull("Process did not complete", kb.getProcessInstance(processInstance.getId()));

		Assert.assertEquals(1, cntInit.getExecuted());
		Assert.assertEquals(2, cntCreateDoc.getExecuted());
	}

	@Test
	public void testSimpleTwoUsers() {
		ConnectionManager c = i.getInstance(ConnectionManager.class);
		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		
		TestCounterHandler cntInit = new TestCounterHandler();
		TestCounterHandler cntCreateDoc = new TestCounterHandler();
		
		kb.registerWorkItemHandler("InitTheo", cntInit);
		kb.registerWorkItemHandler("CreateDoc", cntCreateDoc);
		
		c.newClient("user1", new MockNetworkSender());
		c.newClient("user2", new MockNetworkSender());
		c.newMessage("user1", "Message-WhoAmI", "Spreadsheet");
		c.newMessage("user2", "Message-WhoAmI", "Spreadsheet");
		c.newMessage("user1", "Message-AlexData", "a.xls");
		c.newMessage("user2", "Message-AlexData", "a.xls");
		c.newMessage("user1", "Message-AlexData", "b.xls");
		c.newMessage("user2", "Message-AlexData", "b.xls");
		c.newMessage("user1", "Message-Disconnect", null);
		c.newMessage("user2", "Message-Disconnect", null);
		
		ProcessInstance user1 = c.getState("user1");
		ProcessInstance user2 = c.getState("user1");

		Assert.assertNull("Process did not complete", kb.getProcessInstance(user1.getId()));
		Assert.assertNull("Process did not complete", kb.getProcessInstance(user2.getId()));

		Assert.assertEquals(2, cntInit.getExecuted());
		Assert.assertEquals(4, cntCreateDoc.getExecuted());
	}
	
	@Test
	public void testForwarding() {
		IConnectionManager c = i.getInstance(ConnectionManager.class);
		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		c.newClient("user1", new MockNetworkSender());

		TestCounterHandler cntInit = new TestCounterHandler();
		TestCounterHandler cntCreateDoc = new TestCounterHandler();
		TestCounterHandler cntForward = new TestCounterHandler();
		kb.registerWorkItemHandler("InitTheo", cntInit);
		kb.registerWorkItemHandler("CreateDoc", cntCreateDoc);
		kb.registerWorkItemHandler("forwardToDoc", cntForward);

		c.newMessage("user1", "Message-WhoAmI", "Spreadsheet");
		c.newMessage("user1", "Message-AlexData", "a.xls");
		c.newMessage("user1", "Message-AlexClick", "100x100");
		Assert.assertEquals(1, cntInit.getExecuted());
		Assert.assertEquals(1, cntCreateDoc.getExecuted());
		Assert.assertEquals(1, cntForward.getExecuted());
	}

}