package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ManagerTest {
	Manager manager;
	Block year, cost, data;
	
	final Logger logger = LoggerFactory.getLogger(ManagerTest.class);

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		year = winData.getYear();
		cost = winData.getCost();
		data = winData.getData();
	}

	@Test
	public void test() {
		List<Block> p1 = manager.getBlocksForPosition(new CellSpaceInformation("Table1",0,2));
				
		assertEquals(1, p1.size()); 
		assertEquals(year, p1.get(0));
		assertEquals(4, p1.get(0).getCells().size());
		
		List<Relation> p2 = manager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(1), new Integer(p2.size()));
		
		List<CellTuple> relation = manager.getCellRelationsForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(1), new Integer(relation.size()));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 0))));
		assertTrue(relation.get(0).contains((new CellSpaceInformation("Table1", 0, 3))));
		assertFalse(relation.get(0).contains((new CellSpaceInformation("Table1", 2, 2))));
	}

}
