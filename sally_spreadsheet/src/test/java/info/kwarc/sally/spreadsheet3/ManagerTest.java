package info.kwarc.sally.spreadsheet3;

import static org.junit.Assert.*;

import java.util.List;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.Relation;


import org.junit.Before;
import org.junit.Test;

public class ManagerTest {

	WinogradData winData;
	
	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		winData.getManager().getSemanticModel().createSemanticValues(winData.getManager().getModel().getRelationsFor(null, null, Relation.RelationType.TYPERELATION), winData.getSpreadsheet());
	}

	@Test
	public void testAddCellToBlock() throws ModelException {
		winData.createSecondWorksheet();
		assertEquals(Message.MessageSubType.SemanticIncomplete, winData.getManager().getSemanticModel().checkBlockForCompleteness(winData.getYear2(), winData.getTypeYear2().getUri(), winData.getSpreadsheet()).getSubType());
		winData.getSpreadsheet().setContent(new CellSpaceInformation("Table2",0,4), "1987", "", ContentValueType.STRING_NUMBER);
		winData.getManager().addCellToBlock(new CellSpaceInformation("Table2",0,4), winData.getYear2());
		assertEquals(Message.MessageSubType.Succeed, winData.getManager().getSemanticModel().checkBlockForCompleteness(winData.getYear2(), winData.getTypeYear2().getUri(), winData.getSpreadsheet()).getSubType());
		winData.getSpreadsheet().setContent(new CellSpaceInformation("Table2",0,5), "1988", "", ContentValueType.STRING_NUMBER);
		List<Message> messages = winData.getManager().addCellToBlock(new CellSpaceInformation("Table2",0,5), winData.getYear2());
		assert(messages.size() == 1);
		assertEquals(Message.MessageType.SemanticModelMsg, messages.get(0).getType());
		assertEquals(Message.MessageSubType.SemanticIncomplete, messages.get(0).getSubType());
		//System.out.println("Values for years: \n" + winData.getManager().getSemanticModel().getAllValuesForURI(winData.getTypeYear().getUri()).toString());
		assertEquals(Message.MessageSubType.SemanticIncomplete, winData.getManager().getSemanticModel().checkBlockForCompleteness(winData.getYear(), winData.getTypeYear().getUri(), winData.getSpreadsheet()).getSubType());
	}


}
