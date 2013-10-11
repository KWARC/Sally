package info.kwarc.sally.spreadsheet3.logic;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.InterfaceMockup;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import org.junit.Before;
import org.junit.Test;

public class RelationInterpreterTest {
	WinogradData winData;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
	}
	
	@Test
	public void testGetDefinition() {
		CellSpaceInformation pos = new CellSpaceInformation("Table1",5,1);
		String definition = RelationInterpreter.getDefinition(winData.getRelationProfit(), 
				winData.getRelationProfit().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), new InterfaceMockup());
		System.out.println(definition);
		assertEquals("<apply>\n  <csymbol cd=\"spsht-arith\">minus</csymbol>\n  <apply>\n    <csymbol cd=\"winograd\">RevenuePerYear</csymbol>\n    <ci>Year 1984 AD</ci>\n  </apply>\n  <apply>\n    <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n    <ci>Year 1984 AD</ci>\n    <ci>Costtype: Total</ci>\n  </apply>\n</apply>\n", definition);
	}

	@Test
	public void testInterprete() {
		CellSpaceInformation pos = new CellSpaceInformation("Table1",2,1);
		String interpretation = RelationInterpreter.interprete(winData.getRelationInput(), 
				winData.getRelationInput().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), winData.getManager().getOntologyInterface().getBuilderML() );
		
		assertEquals("<apply>\n<csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n<ci>Year 1984 AD</ci>\n<ci>Costtype: Materials</ci>\n</apply>", interpretation);
	}

}
