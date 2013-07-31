package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.spreadsheet.WorksheetDocument;
import info.kwarc.sally.spreadsheet.injection.SpreadsheetModule;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import com.google.inject.Guice;
import com.google.inject.Injector;

import sally.CellPosition;
import sally.SpreadsheetModel;

public class WorksheetDocumentTest {


	Injector i;
	
	WorksheetDocument doc;

	@Before
	public void setup() {
		i = Guice.createInjector(new SpreadsheetModule());
		try {
			FileInputStream file = new FileInputStream(new File("iui-model.bin"));
			WorksheetFactory wf = i.getInstance(WorksheetFactory.class);
			doc = wf.create("http://iui-paper", SpreadsheetModel.parseFrom(file));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void serializationTest() {
		int workSheetid = doc.getSheetId("Vendor A");
		Assert.assertEquals("https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread", doc.getSemantics(CellPosition.newBuilder().setSheet(workSheetid).setRow(8).setCol(2).build()));
		Assert.assertEquals(null, doc.getSemantics(CellPosition.newBuilder().setSheet(workSheetid).setRow(9).setCol(9).build()));
		CellPosition pos = doc.getPositionFromMMTURI("https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread");
		//Assert.assertEquals(pos.getSheet(), workSheetid);
		Assert.assertEquals(pos.getRow(), 8);
		Assert.assertEquals(pos.getCol(), 2);
	}
}
