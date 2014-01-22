package info.kwarc.sally.spreadsheet3.logic;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.InterfaceMockup;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;

import org.junit.Before;
import org.junit.Test;

public class RelationInterpreterTest {
	WinogradData winData;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
	}
	
	@Test
	public void testGetDefinition() throws ModelException {
		CellSpaceInformation pos = new CellSpaceInformation("Table1",5,1);
		String definition = RelationInterpreter.getDefinition(winData.getRelationProfit(), 
				winData.getRelationProfit().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), new InterfaceMockup());
		
		assertEquals("<apply>\n  <csymbol cd=\"spsht-arith\">minus</csymbol>\n  <apply>\n    <csymbol cd=\"sax-revenues\">sax-revenuesperti</csymbol>\n    <ci>Year 1984 AD</ci>\n  </apply>\n  <apply>\n    <csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n    <ci>Year 1984 AD</ci>\n    <ci>Total Costs</ci>\n  </apply>\n</apply>\n", definition);
		
		/*winData.createSecondeTCRelation();
		pos = new CellSpaceInformation("Table1",4,1);
		definition = RelationInterpreter.getDefinition(winData.getRelationTotalCosts2(), 
				winData.getRelationTotalCosts2().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), new InterfaceMockup());
		*/
		
	}

	@Test
	public void testInterprete() throws ModelException {
		CellSpaceInformation pos = new CellSpaceInformation("Table1",2,1);
		String interpretation = RelationInterpreter.interprete(winData.getRelationCosts(), 
				winData.getRelationCosts().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), winData.getManager().getOntology() );
		
		assertEquals("<apply>\n<csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n<ci>Year 1984 AD</ci>\n<ci>Material Costs</ci>\n</apply>", interpretation);
		
		pos = new CellSpaceInformation("Table1",4,1);
		interpretation = RelationInterpreter.interprete(winData.getRelationTotalCosts(), 
				winData.getRelationTotalCosts().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), winData.getManager().getOntology() );
		assertEquals("<apply>\n<csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n<ci>Year 1984 AD</ci>\n<ci>Total Costs</ci>\n</apply>", interpretation);
		
		winData.createSecondeTCRelation();
		interpretation = RelationInterpreter.interprete(winData.getRelationTotalCosts2(), 
				winData.getRelationTotalCosts2().getCellRelationFor(pos).get(0),
				winData.getSpreadsheet(), winData.getManager().getOntology() );
		assertEquals("<apply>\n<csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n<ci>Year 1984 AD</ci>\n<ci>Total Costs</ci>\n</apply>", interpretation);
		
	}

}
