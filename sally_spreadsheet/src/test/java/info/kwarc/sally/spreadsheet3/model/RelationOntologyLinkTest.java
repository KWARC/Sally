package info.kwarc.sally.spreadsheet3.model;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.WinogradData;

import org.junit.Before;
import org.junit.Test;

public class RelationOntologyLinkTest {
	WinogradData winData;
	
	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
	}

	@Test
	public void test() throws ModelException {
		winData.createSecondeTCRelation();
		
		Relation tc = winData.getRelationTotalCosts2();
		
	}

}
