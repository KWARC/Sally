package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.injection.Configuration;
import info.kwarc.sissi.bpm.injection.ProductionKnowledgeBase;
import info.kwarc.sissi.bpm.injection.ProductionSallyActions;

import java.io.File;
import java.io.FileInputStream;

import sally.SemanticData;
import sally.SpreadsheetModel;
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
				new ProductionKnowledgeBase(), 
				new ProductionSallyActions()
		);
		
		ConnectionManager conn = i.getInstance(ConnectionManager.class);

		conn.newClient("abc");
		conn.newMessage("abc", MessageUtils.createDesktopSpreadsheetAlex());

		FileInputStream file = new FileInputStream(new File("iui-model.bin"));
		SemanticData semData = SemanticData.newBuilder().setSpreadsheetModel(SpreadsheetModel.parseFrom(file)).setFileName("test.xsl").build();
		conn.newMessage("abc", semData);
		
		conn.newMessage("abc", "onDisconnect", null);
	}

}