package info.kwarc.sally;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.injection.Configuration;
import info.kwarc.sally.networking.CometD;
import info.kwarc.sally.networking.Injection.ProductionNetworking;
import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.networking.interfaces.MockNetworkSender;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sally.spreadsheet.ASMEditor;
import info.kwarc.sissi.bpm.injection.ProductionRemoteKnowledgeBase;
import info.kwarc.sissi.bpm.injection.ProductionSallyActions;
import sally.AlexClick;
import sally.AlexData;
import sally.RangeSelection;
import sally.SallyFrame;
import sally.ScreenCoordinates;
import sally_comm.MessageUtils;

import com.google.inject.Guice;
import com.google.inject.Injector;

/**
 * This is a sample file to launch a process.
 */
public class ProcessMain {

	public static final void main(String[] args) throws Exception {
		Injector i = Guice.createInjector(
				new Configuration(),
				new ProductionRemoteKnowledgeBase(), 
				//new ProductionLocalKnowledgeBase(), 
				new ProductionSallyActions(),
				new ProductionNetworking()
		);
		
		SallyInteraction interaction = i.getInstance(SallyInteraction.class);
		interaction.registerServices(i.getInstance(Planetary.class));
		interaction.registerServices(i.getInstance(PricingService.class));
		interaction.registerServices(i.getInstance(InstanceService.class));
		interaction.registerServices(i.getInstance(ASMEditor.class));		

		ISallyWorkflowManager kb = i.getInstance(ISallyWorkflowManager.class);
		//kb.startProcess(null, "Sally.browse_ontology");
		IConnectionManager conn = i.getInstance(IConnectionManager.class);

		CometD cometD = i.getInstance(CometD.class);
		cometD.start();

		//ConnectionPlayer player = i.getInstance(IConnectionPlayerFactory.class).create(new FileReader("rec_spreadsheet.json"));
		//player.start();

		
		
		conn.newClient("spread", new MockNetworkSender());
		conn.newMessage("spread", MessageUtils.createDesktopSpreadsheetAlex());

		AlexData alexData = AlexData.newBuilder().setFileName("file://pipe-end.xls").setData("").build();
		conn.newMessage("spread", alexData);

		AlexClick click = AlexClick.newBuilder().setFileName("file://pipe-end.xls").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).setSheet("Vendor A")
				.setRange(RangeSelection.newBuilder().setStartCol(1).setEndCol(1).setStartRow(8).setEndRow(8).setSheet("Vendor A").build()).build();
		conn.newMessage("spread", click);

		SallyFrame frame =  SallyFrame.newBuilder().setFileName("file://pipe-end.xls").build();
		conn.newMessage("spread", frame);


		//Theo t = i.getInstance(Theo.class);
		//t.openWindow(0L, "hello", "http://localhost:8181/sally/test/test.html", 500, 500);
		
		
		/*
		conn.newClient("cad");
		conn.newMessage("cad", MessageUtils.createDesktopCADAlex());

		AlexData cadAlexData = AlexData.newBuilder().setFileName("pipe-end.iam").setData("Ci9EOlxrd2FyY1xGb3JtYWxDQURcRXhhbXBsZXNcbW9kZWxzXHBpcGUtZW5kLmlhbRLwCwoEcm9vdBoTChFjb3JydWdhdGVkLXBpcGU6MRp7Cg5ibGluZCBmbGFuZ2U6MRJpaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL2ZsYW5nZS1ib2x0LWdhc2tldC5vbWRvYz9mbGFuZ2UtYm9sdC1nYXNrZXQ/YmxpbmQtZmxhbmdlGmEKBmJvbHQ6MRJLaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL251dGJvbHQub21kb2M/bnV0Ym9sdD9ib2x0IgoKBGFyZzESAjEwGmsKBW51dDoxElZodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4bnV0Lm9tZG9jP0lTT2hleG51dD9JU08taGV4LW51dCIKCgRhcmcxEgIxMBp2CghnYXNrZXQ6MRJqaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL2ZsYW5nZS1ib2x0LWdhc2tldC5vbWRvYz9mbGFuZ2UtYm9sdC1nYXNrZXQ/ZmxhbmdlLWdhc2tldBphCgZib2x0OjISS2h0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9udXRib2x0Lm9tZG9jP251dGJvbHQ/Ym9sdCIKCgRhcmcxEgIxMBprCgVudXQ6MhJWaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleG51dC5vbWRvYz9JU09oZXhudXQ/SVNPLWhleC1udXQiCgoEYXJnMRICMTAaYQoGYm9sdDozEktodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvbnV0Ym9sdC5vbWRvYz9udXRib2x0P2JvbHQiCgoEYXJnMRICMTAaawoFbnV0OjMSVmh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXhudXQub21kb2M/SVNPaGV4bnV0P0lTTy1oZXgtbnV0IgoKBGFyZzESAjEwGmEKBmJvbHQ6NBJLaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL251dGJvbHQub21kb2M/bnV0Ym9sdD9ib2x0IgoKBGFyZzESAjEwGmsKBW51dDo0ElZodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4bnV0Lm9tZG9jP0lTT2hleG51dD9JU08taGV4LW51dCIKCgRhcmcxEgIxMBphCgZib2x0OjUSS2h0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9udXRib2x0Lm9tZG9jP251dGJvbHQ/Ym9sdCIKCgRhcmcxEgIxMBprCgVudXQ6NRJWaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleG51dC5vbWRvYz9JU09oZXhudXQ/SVNPLWhleC1udXQiCgoEYXJnMRICMTAaYQoGYm9sdDo2EktodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvbnV0Ym9sdC5vbWRvYz9udXRib2x0P2JvbHQiCgoEYXJnMRICMTAaawoFbnV0OjYSVmh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXhudXQub21kb2M/SVNPaGV4bnV0P0lTTy1oZXgtbnV0IgoKBGFyZzESAjEw").build();
		conn.newMessage("cad", cadAlexData);

		SallyInteraction sally = i.getInstance(SallyInteraction.class);
		List<Model> models = sally.getPossibleInteractions("/get/semantics", new SallyModelRequest(), Model.class);
		Model common = ModelFactory.createDefaultModel();
		for (Model mod : models) {
			common.add(mod);
		}
		
		FileOutputStream file = new FileOutputStream("cad-model.rdf");
		common.write(file);
		file.close();
		
	*/
/*
		while (true) {
			Thread.sleep(1000);

			click = AlexClick.newBuilder().setFileName("file://pipe-end.xls").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).setSheet("Vendor A")
					.setRange(RangeSelection.newBuilder().setStartCol(2).setEndCol(2).setStartRow(8).setEndRow(8).setSheet("Vendor A").build()).build();
			conn.newMessage("spread", click);
		}
*/

		
		/*
		
		CADAlexClick click = CADAlexClick.newBuilder().setFileName("pipe-end.iam").setCadNodeId("nut:1").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).build();
		conn.newMessage("cad", click);

		SallyFrame frame =  SallyFrame.newBuilder().setFileName("pipe-end.iam").build();
		conn.newMessage("cad", frame);
*/

		/*
		while (true) {
			Thread.sleep(5000);
			CADAlexClick click = CADAlexClick.newBuilder().setFileName("pipe-end.iam").setCadNodeId("nut:1").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).build();
			conn.newMessage("cad", click);

			SallyFrame frame =  SallyFrame.newBuilder().setFileName("pipe-end.iam").build();
			conn.newMessage("cad", frame);
		}
		
*/
		//conn.close();
		//BPMNUtils.showStatus(i.getInstance(ISallyKnowledgeBase.class).getKnowledgeSession());
	}

}