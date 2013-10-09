package info.kwarc.sally.spreadsheet3.model;

import static org.junit.Assert.*;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;

import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ManagerTest {
	Manager manager;
	FormalSpreadsheet spreadsheet;
	Block year;
	
	final Logger logger = LoggerFactory.getLogger(ManagerTest.class);

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
		year = winData.getYear();

	}

	@Test
	public void test() {
		List<Block> p1 = manager.getBlocksForPosition(new CellSpaceInformation("Table1",0,2));
				
		assertEquals(1, p1.size()); 
		assertEquals(year, p1.get(0));
		assertEquals(4, p1.get(0).getCells().size());
		
		List<Relation> p2 = manager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(2), new Integer(p2.size()));
		
		List<CellTuple> relation = manager.getCellRelationsForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(2), new Integer(relation.size()));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 0))));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 0, 3))));
		assertFalse(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 2))));
		
		Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
		assertEquals("<ci>Year 1985 AD</ci>", interpretation.get(new CellSpaceInformation("Table1", 0, 2)));
		assertEquals("<ci>Costtype: total</ci>", interpretation.get(new CellSpaceInformation("Table1", 4, 0)));
		assertEquals("<apply>\n" +
				"<csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"<ci>Year 1985 AD</ci>\n" +
				"<ci>Costtype: total</ci>\n" +
				"</apply>", interpretation.get(new CellSpaceInformation("Table1", 4,2)));
	}
	
	@Test
	public void testSerialize() {
		// Atomic Block test
		Block atomicBlock = manager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",0,3));
		Block atomicBlockNew = Block.createBlockFromMessage(atomicBlock.serialize(), manager);
		assertEquals(atomicBlock, atomicBlockNew);
		
		Block composedBlock = manager.getBlocksForPosition(new CellSpaceInformation("Table1",0,3)).get(0);
		Block composedBlockNew = Block.createBlockFromMessage(composedBlock.serialize(), manager);
		assertEquals(composedBlock, composedBlockNew);
		
		// Relation Test
		Relation rel = manager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3)).get(0);
		Relation relNew = new Relation(rel.serialize(), manager);
		assertEquals(rel, relNew);
				
		// Model Test
		sally.ModelDataMsgNew modelData = manager.serialize();
		Manager managerNew = new Manager(manager.getOntologyInterface(), modelData);

		assertEquals(manager, managerNew);
	}

}
