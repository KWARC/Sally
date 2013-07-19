package info.kwarc.sally;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.comm.SallyModelRequest;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sally.spreadsheet.ASMEditor;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import info.kwarc.sally.spreadsheet.WorksheetFactory;
import info.kwarc.sally.theofx.TheoService;
import info.kwarc.sissi.model.document.cad.CADDocument;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.List;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

public class Sally {
	
	static void export(SallyInteraction sally) {
		Model common = ModelFactory.createDefaultModel();
		List<Model> models = sally.getPossibleInteractions("/get/semantics", new SallyModelRequest(), Model.class);
		for (Model mod : models) {
			common.add(mod);
		}
		OutputStream file;
		try {
			file = new FileOutputStream("all.rdf");
			common.write(file);
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		SallyInteraction sally = new SallyInteraction();
		CometD cometD = new CometD(8080);
		cometD.start();
		cometD.channelToInteraction(sally);

		sally.registerServices(new TheoService());
		sally.registerServices(new Planetary("http://localhost/planetary", "sallyrpc", "test", "123"));
		sally.registerServices(cometD);
		sally.registerServices(new WorksheetFactory());

		WorksheetDocument spreadDoc = new WorksheetDocument();
		spreadDoc.setSemanticData("iui-model.bin");

		CADDocument cadDoc = new CADDocument();
		cadDoc.setSemanticData("cad-model.bin");
		
		sally.registerServices(spreadDoc);
		sally.registerServices(cadDoc);
		sally.registerServices(new PricingService());
		sally.registerServices(new ASMEditor());

		export(sally);

		/* CADAlexClick click = CADAlexClick.newBuilder().setFileName("http://blah.cad").setCadNodeId("bolt1").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).build();
		sally.getPossibleInteractions("/service/alex/selectRange", click, MMTUri.class); */
		
		/* AlexClick click = AlexClick.newBuilder().setFileName("http://default-doc.xls").setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build()).setSheet("Vendor A")
					.setRange(RangeSelection.newBuilder().setSheet("Vendor B").setStartRow(8).setEndRow(8).setStartCol(7).setEndCol(12).build()).build();
		sally.getPossibleInteractions("/service/alex/selectRange", click, MMTUri.class); */
		
		/*
		RangeSelection sel = RangeSelection.newBuilder().setSheet("Vendor B").setStartRow(8).setEndRow(8).setStartCol(7).setEndCol(12).build();
		SallyMenuItem e = sally.getOneInteraction(sel, SallyMenuItem.class);
		e.run();
		*/
	}
	
}
