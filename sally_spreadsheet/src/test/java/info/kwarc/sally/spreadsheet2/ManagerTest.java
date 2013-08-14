package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ManagerTest {
	Manager manager;
	Block year, cost, data;
	Relation relationID;
	
	final Logger logger = LoggerFactory.getLogger(ManagerTest.class);

	@Before
	public void setUp() throws Exception {
		manager = new Manager(WinogradData.getFormalWinograd());
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table1",1,1), new CellSpaceInformation("Table1",1,4));
		year = manager.createComposedBlock(positionYear);
		logger.info("YearID: " + year.getId());
		
		List<CellSpaceInformation> positionCosts = Util.expandRange(
				new CellSpaceInformation("Table1",2,0), new CellSpaceInformation("Table1",4,0));
		cost = manager.createComposedBlock(positionCosts);
		logger.info("CostID: " + cost.getId());
		
		List<CellSpaceInformation> positionData = Util.expandRange(
				new CellSpaceInformation("Table1",2,1), new CellSpaceInformation("Table1",4,4));
		data = manager.createComposedBlock(positionData);
		logger.info("dataID: " + data.getId());
		
		List<Block> blocks = new ArrayList<Block>();
		blocks.add(year);
		blocks.add(cost);
		blocks.add(data);

 		relationID = manager.createFunctionalRelation(blocks, "");
	}

	@Test
	public void test() {
		List<Block> p1 = manager.getBlocksForPosition(new CellSpaceInformation("Table1",1,2));
				
		assertEquals(2, p1.size());   // One atomic and one componded
		assertEquals(year, p1.get(1));
		assertEquals(4, p1.get(1).getCells().size());
		
		List<Relation> p2 = manager.getRelationForPosition(new CellSpaceInformation("Table1", 2, 3));
		assertEquals(new Integer(1), new Integer(p2.size()));
	}

}
