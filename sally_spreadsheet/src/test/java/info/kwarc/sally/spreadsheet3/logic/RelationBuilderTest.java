package info.kwarc.sally.spreadsheet3.logic;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.BlockAtomic;
import info.kwarc.sally.spreadsheet3.model.BlockComposed;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

public class RelationBuilderTest {

	@Before
	public void setUp() throws Exception {
	}

	@Test
	public void testCreateCellRelation() {
		List<Block> topBlocks = new ArrayList<Block>();
		
		List<CellSpaceInformation> p1 = new ArrayList<CellSpaceInformation>();
		p1.add(new CellSpaceInformation("tab1", 0 , 0));
		p1.add(new CellSpaceInformation("tab1", 0 , 1));
		p1.add(new CellSpaceInformation("tab1", 0 , 2));
		
		List<Block> blocks1 = new ArrayList<Block>();
		for (CellSpaceInformation pos : p1)
			blocks1.add(new BlockAtomic(0, pos));
		Block block1 = new BlockComposed(0, blocks1);
		
		topBlocks.add(block1);
		
		List<CellSpaceInformation> p2 = new ArrayList<CellSpaceInformation>();
		p2.add(new CellSpaceInformation("tab1", 1 , 0));
		p2.add(new CellSpaceInformation("tab1", 2 , 0));
		p2.add(new CellSpaceInformation("tab1", 3 , 0));
		
		List<Block> blocks2 = new ArrayList<Block>();
		for (CellSpaceInformation pos : p2)
			blocks2.add(new BlockAtomic(0, pos));
		Block block2 = new BlockComposed(0, blocks2);
		
		topBlocks.add(block2);
		
		List<CellSpaceInformation> p3 = new ArrayList<CellSpaceInformation>();
		p3.add(new CellSpaceInformation("tab1", 1 , 1));
		p3.add(new CellSpaceInformation("tab1", 1 , 2));
		p3.add(new CellSpaceInformation("tab1", 1 , 3));
		p3.add(new CellSpaceInformation("tab1", 2 , 1));
		p3.add(new CellSpaceInformation("tab1", 2 , 2));
		p3.add(new CellSpaceInformation("tab1", 2 , 3));
		p3.add(new CellSpaceInformation("tab1", 3 , 1));
		p3.add(new CellSpaceInformation("tab1", 3 , 2));
		p3.add(new CellSpaceInformation("tab1", 3 , 3));
		
		List<Block> blocks3 = new ArrayList<Block>();
		for (CellSpaceInformation pos : p3)
			blocks3.add(new BlockAtomic(0, pos));
		Block block3 = new BlockComposed(0, blocks3);
		
		topBlocks.add(block3);
		
		List<CellDependencyDescription> descriptions = new ArrayList<CellDependencyDescription>();
		descriptions.add(new CellDependencyDescription(1,3,1,3,"0,y-1;x-1,0;x-1,y-1"));
		
		List<CellTuple> tuples = RelationBuilder.createCellRelation(topBlocks, descriptions);
		assertTrue(tuples.size() == 9);
		assertEquals(tuples.get(0).getTuple().get(2), new CellSpaceInformation("tab1",1,1));
		assertEquals(tuples.get(1).getTuple().get(0), new CellSpaceInformation("tab1",0,1));
		assertEquals(tuples.get(3).getTuple().get(1), new CellSpaceInformation("tab1",2,0));
	}

}
