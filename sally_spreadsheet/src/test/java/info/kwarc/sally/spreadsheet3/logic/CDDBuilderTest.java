package info.kwarc.sally.spreadsheet3.logic;

import static org.junit.Assert.assertEquals;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

public class CDDBuilderTest {
	WinogradData winograd;

	@Before
	public void setUp() throws Exception {
		winograd = new WinogradData();
	}

	@Test
	public void testCreateCDDFunctionalRelation() {
		List<Block> blocks = new ArrayList<Block>();
		blocks.add(winograd.getCost());
		blocks.add(winograd.getYear());
		blocks.add(winograd.getDataCosts());
		
		assertEquals("(0/0 - 2/3): 0,y;x,0;x,y", CDDBuilder.createCDDFunctionalRelation(blocks).toString());
	}

}
