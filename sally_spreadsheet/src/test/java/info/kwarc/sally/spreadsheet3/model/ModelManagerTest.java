package info.kwarc.sally.spreadsheet3.model;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;

import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ModelManagerTest {
	ModelManager modelManager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	
	final Logger logger = LoggerFactory.getLogger(ModelManagerTest.class);

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		modelManager = winData.getModelManager();
		spreadsheet = winData.getSpreadsheet();
	}

	@Test
	public void test() throws ModelException {
		List<Block> p1 = modelManager.getBlocksForPosition(new CellSpaceInformation("Table1",0,2));
				
		assertEquals(1, p1.size()); 
		assertEquals(winData.getYear(), p1.get(0));
		assertEquals(4, p1.get(0).getCells().size());
		
		List<Relation> p2 = modelManager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(2), new Integer(p2.size()));
		
		List<CellTuple> relation = modelManager.getCellRelationsForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(2), new Integer(relation.size()));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 0))));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 0, 3))));
		assertFalse(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 2))));
		
		Map<CellSpaceInformation, String> interpretation = modelManager.getCompleteSemanticMapping(spreadsheet, winData.getManager().getOntology());
		assertEquals("<ci>Year 1985 AD</ci>", interpretation.get(new CellSpaceInformation("Table1", 0, 2)));
		assertEquals("<ci>Total Costs</ci>", interpretation.get(new CellSpaceInformation("Table1", 4, 0)));
		assertEquals("<apply>\n" +
				"<csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n" +
				"<ci>Year 1985 AD</ci>\n" +
				"<ci>Total Costs</ci>\n" +
				"</apply>", interpretation.get(new CellSpaceInformation("Table1", 4,2)));
	}
	
	@Test
	public void testSerialize() throws ModelException {
		// Atomic Block test
		Block atomicBlock = modelManager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",0,3));
		Block atomicBlockNew = Block.createBlockFromMessage(atomicBlock.serialize(), modelManager);
		assertEquals(atomicBlock, atomicBlockNew);
		
		Block composedBlock = modelManager.getBlocksForPosition(new CellSpaceInformation("Table1",0,3)).get(0);
		Block composedBlockNew = Block.createBlockFromMessage(composedBlock.serialize(), modelManager);
		assertEquals(composedBlock, composedBlockNew);
		
		// Relation Test
		Relation rel = modelManager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3)).get(0);
		Relation relNew = new Relation(rel.serialize(), modelManager);
		assertEquals(rel, relNew);
				
		// Model Test
		sally.ModelDataMsg modelData = modelManager.serialize();
		ModelManager managerNew = new ModelManager(modelData);

		assertEquals(modelManager, managerNew);
	}
	
	@Test
	public void testRemove() {
		int numberOfBlocks = modelManager.getAllBlocks().size();
		int numberOfRelations = modelManager.getAllRelations().size();
		modelManager.removeBlock(winData.getYear());
		assertTrue(modelManager.getAllBlocks().size() == (numberOfBlocks - 1) );
		assertTrue(modelManager.getAllRelations().size() == (numberOfRelations - 5)); // typeYear, revenues, costs, total costs, profit
	}
	

}
