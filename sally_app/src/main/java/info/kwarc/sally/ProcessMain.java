package info.kwarc.sally;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.comm.SallyModelRequest;
import info.kwarc.sally.injection.Configuration;
import info.kwarc.sally.networking.CometD;
import info.kwarc.sally.networking.Injection.ProductionNetworking;
import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sally.spreadsheet.ASMEditor;
import info.kwarc.sissi.bpm.injection.ProductionLocalKnowledgeBase;
import info.kwarc.sissi.bpm.injection.ProductionSallyActions;

import java.io.FileOutputStream;
import java.util.List;

import sally.AlexData;
import sally.CADAlexClick;
import sally.SallyFrame;
import sally.ScreenCoordinates;
import sally_comm.MessageUtils;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

/**
 * This is a sample file to launch a process.
 */
public class ProcessMain {

	public static final void main(String[] args) throws Exception {
		Injector i = Guice.createInjector(
				new Configuration(),
				//new ProductionRemoteKnowledgeBase(), 
				new ProductionLocalKnowledgeBase(), 
				new ProductionSallyActions(),
				new ProductionNetworking()
		);

		SallyInteraction interaction = i.getInstance(SallyInteraction.class);
		interaction.registerServices(i.getInstance(Planetary.class));
		interaction.registerServices(i.getInstance(PricingService.class));
		interaction.registerServices(i.getInstance(ASMEditor.class));
		
		IConnectionManager conn = i.getInstance(IConnectionManager.class);

		CometD cometD = i.getInstance(CometD.class);
		cometD.start();

		//ConnectionPlayer player = i.getInstance(IConnectionPlayerFactory.class).create(new FileReader("rec_spreadsheet.json"));
		//player.start();

		conn.newClient("spread");
		conn.newMessage("spread", MessageUtils.createDesktopSpreadsheetAlex());

		AlexData alexData = AlexData.newBuilder().setFileName("file://pipe-end.xls").setData("").build();
		conn.newMessage("spread", alexData);

		conn.newClient("cad");
		conn.newMessage("cad", MessageUtils.createDesktopCADAlex());

		alexData = AlexData.newBuilder().setFileName("pipe-end.iam").setData("Ci9EOlxrd2FyY1xGb3JtYWxDQURcRXhhbXBsZXNcbW9kZWxzXHBpcGUtZW5kLmlhbRLwCwoEcm9vdBoTChFjb3JydWdhdGVkLXBpcGU6MRp7Cg5ibGluZCBmbGFuZ2U6MRJpaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL2ZsYW5nZS1ib2x0LWdhc2tldC5vbWRvYz9mbGFuZ2UtYm9sdC1nYXNrZXQ/YmxpbmQtZmxhbmdlGmEKBmJvbHQ6MRJLaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL251dGJvbHQub21kb2M/bnV0Ym9sdD9ib2x0IgoKBGFyZzESAjEwGmsKBW51dDoxElZodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4bnV0Lm9tZG9jP0lTT2hleG51dD9JU08taGV4LW51dCIKCgRhcmcxEgIxMBp2CghnYXNrZXQ6MRJqaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL2ZsYW5nZS1ib2x0LWdhc2tldC5vbWRvYz9mbGFuZ2UtYm9sdC1nYXNrZXQ/ZmxhbmdlLWdhc2tldBphCgZib2x0OjISS2h0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9udXRib2x0Lm9tZG9jP251dGJvbHQ/Ym9sdCIKCgRhcmcxEgIxMBprCgVudXQ6MhJWaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleG51dC5vbWRvYz9JU09oZXhudXQ/SVNPLWhleC1udXQiCgoEYXJnMRICMTAaYQoGYm9sdDozEktodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvbnV0Ym9sdC5vbWRvYz9udXRib2x0P2JvbHQiCgoEYXJnMRICMTAaawoFbnV0OjMSVmh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXhudXQub21kb2M/SVNPaGV4bnV0P0lTTy1oZXgtbnV0IgoKBGFyZzESAjEwGmEKBmJvbHQ6NBJLaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL251dGJvbHQub21kb2M/bnV0Ym9sdD9ib2x0IgoKBGFyZzESAjEwGmsKBW51dDo0ElZodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvSVNPaGV4bnV0Lm9tZG9jP0lTT2hleG51dD9JU08taGV4LW51dCIKCgRhcmcxEgIxMBphCgZib2x0OjUSS2h0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9udXRib2x0Lm9tZG9jP251dGJvbHQ/Ym9sdCIKCgRhcmcxEgIxMBprCgVudXQ6NRJWaHR0cHM6Ly90bnQua3dhcmMuaW5mby9yZXBvcy9zdGMvZmNhZC9mbGFuZ2UvY2RzL0lTT2hleG51dC5vbWRvYz9JU09oZXhudXQ/SVNPLWhleC1udXQiCgoEYXJnMRICMTAaYQoGYm9sdDo2EktodHRwczovL3RudC5rd2FyYy5pbmZvL3JlcG9zL3N0Yy9mY2FkL2ZsYW5nZS9jZHMvbnV0Ym9sdC5vbWRvYz9udXRib2x0P2JvbHQiCgoEYXJnMRICMTAaawoFbnV0OjYSVmh0dHBzOi8vdG50Lmt3YXJjLmluZm8vcmVwb3Mvc3RjL2ZjYWQvZmxhbmdlL2Nkcy9JU09oZXhudXQub21kb2M/SVNPaGV4bnV0P0lTTy1oZXgtbnV0IgoKBGFyZzESAjEw").build();
		conn.newMessage("cad", alexData);

		
		SallyInteraction sally = i.getInstance(SallyInteraction.class);
		List<Model> models = sally.getPossibleInteractions("/get/semantics", new SallyModelRequest(), Model.class);
		Model common = ModelFactory.createDefaultModel();
		for (Model mod : models) {
			common.add(mod);
		}
		System.out.println(common.toString());
		
		FileOutputStream file = new FileOutputStream("cad-model.rdf");
		common.write(file);
		file.close();
		
		CADAlexClick click = CADAlexClick.newBuilder().setFileName("pipe-end.iam").setCadNodeId("bolt:1").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).build();
		conn.newMessage("cad", click);

		SallyFrame frame =  SallyFrame.newBuilder().setFileName("pipe-end.iam").build();
		conn.newMessage("cad", frame);
		
		//conn.close();
		//BPMNUtils.showStatus(i.getInstance(ISallyKnowledgeBase.class).getKnowledgeSession());
	}

}