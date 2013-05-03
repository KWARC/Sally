package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyModelRequest;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.planetary.Planetary;
import info.kwarc.sally.theofx.TheoService;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import sally.SpreadsheetModel;

import com.hp.hpl.jena.rdf.model.Model;

public class IUIMain {
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
		
		//Model bigModel = 
		List<Model> q = sally.getPossibleInteractions("/get/semantics", new SallyModelRequest(), Model.class);
		System.out.println(q.size());
	}
}
