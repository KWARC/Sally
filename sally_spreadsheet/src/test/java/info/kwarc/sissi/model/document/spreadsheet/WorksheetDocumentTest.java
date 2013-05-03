package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sissi.spreadsheet.WorksheetDocument;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import sally.CellPosition;
import sally.SpreadsheetModel;

public class WorksheetDocumentTest {

	WorksheetDocument doc;

	@Before
	public void setup() {
		try {
			FileInputStream file = new FileInputStream(new File("iui-model.bin"));
			doc = new WorksheetDocument("http://iui-paper");
			doc.setSemanticData(SpreadsheetModel.parseFrom(file));
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
