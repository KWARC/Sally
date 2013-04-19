package info.kwarc.sissi.spreadsheet;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sally.theofx.TheoService;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import sally.AlexClick;
import sally.RangeSelection;
import sally.ScreenCoordinates;
import sally.SpreadsheetModel;

public class WorksheetMain {
	public static void main(String[] args) {
		SallyInteraction sally = new SallyInteraction();
		CometD cometD = new CometD(8080);
		cometD.start();
		cometD.channelToInteraction(sally);
		
		sally.registerServices(new TheoService());
		sally.registerServices(new Planetary("http://localhost/drupal_planetary", "sally", "test", "123"));
		sally.registerServices(cometD);
		sally.registerServices(new WorksheetFactory());
		
		WorksheetDocument doc = new WorksheetDocument("http://iui-paper");
		
		try {
			FileInputStream file = new FileInputStream(new File("iui-model.bin"));
			doc.setSemanticData(SpreadsheetModel.parseFrom(file));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		sally.registerServices(doc);
		System.out.println(sally.toString());
		
		AlexClick click = AlexClick.newBuilder().setFileName("http://iui-paper").setSheet("Vendor A")
			.setRange(RangeSelection.newBuilder().setSheet("Vendor A").setStartCol(2).setStartRow(8).setEndCol(2).setEndRow(8).build())
			.setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build())
			.build();
		
		sally.getOneInteraction("/service/alex/selectRange", click, Boolean.class);
		
	}
}
