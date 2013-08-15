package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.core.ScreenCoordinatesProvider;
import info.kwarc.sally.core.interfaces.IPositionProvider;
import info.kwarc.sally.networking.interfaces.IMessageCallback;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import sally.CellPosition;
import sally.SpreadsheetModel;

import com.google.inject.AbstractModule;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.assistedinject.FactoryModuleBuilder;
import com.google.protobuf.AbstractMessage;

public class WorksheetDocumentTest {
	Injector i;
	
	WorksheetDocument doc;
	
	@Before
	public void setup() {
		i = Guice.createInjector(new AbstractModule() {

			@Override
			protected void configure() {
				bind(IPositionProvider.class).to(ScreenCoordinatesProvider.class);
				install(new FactoryModuleBuilder().build(WorksheetFactory.class));
			}
		});
	}

	@Test
	public void serializationTest() {
		try {
			FileInputStream file = new FileInputStream(new File("iui-model.bin"));
			WorksheetFactory wf = i.getInstance(WorksheetFactory.class);
			doc = wf.create("http://iui-paper", SpreadsheetModel.parseFrom(file), new INetworkSender() {
				
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
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		int workSheetid = doc.getSheetId("Vendor A");
		Assert.assertEquals("https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexbolt", doc.getSemantics(CellPosition.newBuilder().setSheet(workSheetid).setRow(8).setCol(2).build()));
		Assert.assertEquals(null, doc.getSemantics(CellPosition.newBuilder().setSheet(workSheetid).setRow(9).setCol(9).build()));
		CellPosition pos = doc.getPositionFromMMTURI("https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?ISOhexbolt");
		//Assert.assertEquals(pos.getSheet(), workSheetid);
		Assert.assertEquals(pos.getRow(), 8);
		Assert.assertEquals(pos.getCol(), 2);
	}
}
