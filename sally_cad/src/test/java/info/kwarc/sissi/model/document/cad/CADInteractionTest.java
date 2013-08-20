package info.kwarc.sissi.model.document.cad;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.injectors.TheoFirstChoice;
import info.kwarc.sally.networking.interfaces.IMessageCallback;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
import info.kwarc.sissi.bpm.injection.TestableKnowledeBase;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;
import info.kwarc.sissi.bpm.tasks.LetUserChoose;
import info.kwarc.sissi.bpm.tasks.RunChoice;
import info.kwarc.sissi.bpm.tasks.TestCounterHandler;
import info.kwarc.sissi.bpm.tasks.TestInputTypeHandler;
import info.kwarc.sissi.model.document.cad.injection.CADModule;
import info.kwarc.sissi.model.document.cad.interfaces.CADFactory;

import java.util.HashMap;

import org.apache.commons.codec.binary.Base64;
import org.drools.KnowledgeBase;
import org.drools.builder.ResourceType;
import org.drools.runtime.process.ProcessInstance;
import org.jbpm.process.instance.impl.demo.SystemOutWorkItemHandler;
import org.jbpm.test.JbpmJUnitTestCase;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import sally.CADAlexClick;
import sally.CADSemanticData;
import sally.MMTUri;
import sally.ScreenCoordinates;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.protobuf.AbstractMessage;

public class CADInteractionTest extends JbpmJUnitTestCase {

	Injector i;
	CADSemanticData alexData;

	@Before
	public void setup() throws Exception {
		HashMap<String, ResourceType> resources = new HashMap<String, ResourceType>();
		resources.put("Sally.pkg", ResourceType.PKG);
		createKnowledgeBase(resources);
		KnowledgeBase b = createKnowledgeBaseGuvnor("Sally");
		String CADBase64 = "Cg9odHRwOi8vYmxhaC5jYWQSqgkKCHBpcGVfZW5kGqUCCgVib2x0MRJXaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleGJvbHQub21kb2M/SVNPaGV4Ym9sdD9JU09oZXhib2x0ImQKXWh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXh0aHJlYWQub21kb2M/SVNPaGV4dGhyZWFkP0lTT2hleHRocmVhZBIDTTE1Il0KVWh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9jb21wb25lbnRzLm9tZG9jP2NvbXBvbmVudD9jb21wb25lbnQSBGJvbHQapQIKBWJvbHQyEldodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4Ym9sdC5vbWRvYz9JU09oZXhib2x0P0lTT2hleGJvbHQiZApdaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleHRocmVhZC5vbWRvYz9JU09oZXh0aHJlYWQ/SVNPaGV4dGhyZWFkEgNNMTUiXQpVaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL2NvbXBvbmVudHMub21kb2M/Y29tcG9uZW50P2NvbXBvbmVudBIEYm9sdBqlAgoFYm9sdDMSV2h0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXhib2x0Lm9tZG9jP0lTT2hleGJvbHQ/SVNPaGV4Ym9sdCJkCl1odHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4dGhyZWFkLm9tZG9jP0lTT2hleHRocmVhZD9JU09oZXh0aHJlYWQSA00xNSJdClVodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvY29tcG9uZW50cy5vbWRvYz9jb21wb25lbnQ/Y29tcG9uZW50EgRib2x0GqUCCgVib2x0NBJXaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleGJvbHQub21kb2M/SVNPaGV4Ym9sdD9JU09oZXhib2x0ImQKXWh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXh0aHJlYWQub21kb2M/SVNPaGV4dGhyZWFkP0lTT2hleHRocmVhZBIDTTE1Il0KVWh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9jb21wb25lbnRzLm9tZG9jP2NvbXBvbmVudD9jb21wb25lbnQSBGJvbHQ=";
		alexData = CADSemanticData.parseFrom(Base64.decodeBase64(CADBase64));
		i = Guice.createInjector(
				new CADModule(),
				new TestableKnowledeBase(createKnowledgeSession(b)),
				new TheoFirstChoice()
				);
	}

	@Test
	public void testWorkflow() {
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);
		HashMap<String, TestCounterHandler> counters = HandlerUtils.registerCounterHandlers(kb, "DynamicApplicability", "LetUserChoose", "RunChoice", "CADSelectionForwarder");
		
		ProcessInstance inst = kb.startProcess(null, "Sally.cad");
		inst.signalEvent("Message-CADAlexClick", null);

		Assert.assertEquals(1, counters.get("CADSelectionForwarder").getExecuted());
		inst.signalEvent("Message-SallyFrame", null);
		Assert.assertEquals(1, counters.get("DynamicApplicability").getExecuted());
		Assert.assertEquals(1, counters.get("LetUserChoose").getExecuted());
		Assert.assertEquals(1, counters.get("RunChoice").getExecuted());
		
		inst.signalEvent("Message-CADAlexClick", null);
		Assert.assertEquals(2, counters.get("CADSelectionForwarder").getExecuted());
	}
	
	@Test
	public void testDAConnections() {
		ISallyKnowledgeBase kb = i.getInstance(ISallyKnowledgeBase.class);

		kb.registerWorkItemHandler("DynamicApplicability", new TestInputTypeHandler(String.class, SallyMenuItem.class));
		kb.registerWorkItemHandler("LetUserChoose", i.getInstance(LetUserChoose.class));
		kb.registerWorkItemHandler("RunChoice", i.getInstance(RunChoice.class));
		kb.registerWorkItemHandler("CADSelectionForwarder", new SystemOutWorkItemHandler());

		SallyInteraction interaction = i.getInstance(SallyInteraction.class);

		CADFactory docFactory = i.getInstance(CADFactory.class);
		CADDocument doc = docFactory.create("test1", alexData, new INetworkSender() {
			
			@Override
			public void sendMessage(String channel, AbstractMessage msg,
					IMessageCallback callback) {
				// TODO Auto-generated method stub
				
			}
			
			@Override
			public void sendMessage(String channel, AbstractMessage msg) {
				// TODO Auto-generated method stub
				
			}
		});
		interaction.registerServices(doc);

		interaction.registerServices(new Object() {
			@SallyService
			public void run(MMTUri input, SallyInteractionResultAcceptor acceptor,
					SallyContext context) {
				acceptor.acceptResult(new SallyMenuItem("frame1", "service1", "") {

					@Override
					public void run() {
						System.out.println("gere");
					}
				});
			}
		});	

		ProcessInstance inst = kb.startProcess(null, "Sally.cad");

		CADAlexClick click = CADAlexClick.newBuilder().setFileName("test.cad").setCadNodeId("bolt1").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).build();
		inst.signalEvent("Message-CADAlexClick", click);
	}	
}