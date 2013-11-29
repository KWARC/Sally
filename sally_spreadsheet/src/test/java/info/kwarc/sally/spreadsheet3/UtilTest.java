package info.kwarc.sally.spreadsheet3;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.RangeInformation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathML;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

public class UtilTest {
	Manager manager;
	ConcreteSpreadsheet spreadsheet;
	psf.ParserInterface parser;
	BuilderML mlBuilder;

	
	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
		parser = new psf.ParserInterface();
		mlBuilder = new BuilderMathML();
	}

	@Test
	public void testRangeParser() {
		RangeInformation ri = Util.convertRangeAddress("Sheet1!C4:F10");
		assertEquals(ri.getWorksheet(), "Sheet1");
		assertEquals(2, ri.getStartRow());
		assertEquals(3, ri.getStartCol());
		assertEquals(5, ri.getEndRow());
		assertEquals(9, ri.getEndCol());
	}
	
	@Test
	public void testAntiunifyMathMLFormulae() {
		// formula parsing
		psf.SemanticMapping mapping = new psf.SemanticMapping();
		Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
		for (CellSpaceInformation pos : interpretation.keySet()) 
			mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
		
		List<String> formulae = new ArrayList<String>();
		psf.ParserParameter p = new psf.ParserParameter("B3+B4", "Table1", false, true, false, true, mapping.getMapping());
		formulae.add(parser.parseFormula(p).getMathML());
		
		p = new psf.ParserParameter("C3+C4", "Table1", false, true, false, true, mapping.getMapping());
		formulae.add(parser.parseFormula(p).getMathML());
		
		p = new psf.ParserParameter("D3+D4", "Table1", false, true, false, true, mapping.getMapping());
		formulae.add(parser.parseFormula(p).getMathML());
		
		p = new psf.ParserParameter("E3+E4", "Table1", false, true, false, true, mapping.getMapping());
		formulae.add(parser.parseFormula(p).getMathML());
		
		
		// Setting up domain Values
		List<List<String>> domainValues = new ArrayList<List<String>>();
		CellSpaceInformation positionTotal = new CellSpaceInformation("Table1",4,0);
		
		List<String> dv1 = new ArrayList<String>();
		CellSpaceInformation position = new CellSpaceInformation("Table1",0,1);
		dv1.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv1.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv1);
		
		List<String> dv2 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,2);
		dv2.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv2.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv2);
		
		List<String> dv3 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,3);
		dv3.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv3.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv3);
		
		List<String> dv4 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,4);
		dv4.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv4.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv4);
		
		String antiunificationResult = Util.antiunifyMathMLFormulae(formulae, domainValues, mlBuilder);
		//System.out.println("Antiunification: \n " + antiunificationResult);
		//assertEquals(418, antiunificationResult.length());
		assertEquals(
				"<math xmlns=\"http://www.w3.org/1998/Math/MathML\">\n" +
				"  <apply>\n" +
				"    <csymbol cd=\"spsht-arith\">plus</csymbol>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"      <rvar num=\"0\"/>\n" +
				"      <ci>Material Costs</ci>\n" +
				"      </apply>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"      <rvar num=\"0\"/>\n" +
				"      <ci>Salary Costs</ci>\n" +
				"      </apply>\n" +
				"  </apply>\n" +
				"</math>", antiunificationResult.replaceAll("\r", "")
				);
		
	}
	
	@Test
	public void testGetConstantArguments() {
		// Setting up domain Values
		List<List<String>> domainValues = new ArrayList<List<String>>();
		CellSpaceInformation positionTotal = new CellSpaceInformation("Table1",4,0);
		
		List<String> dv1 = new ArrayList<String>();
		CellSpaceInformation position = new CellSpaceInformation("Table1",0,1);
		dv1.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv1.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv1);
		
		List<String> dv2 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,2);
		dv2.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv2.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv2);
		
		List<String> dv3 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,3);
		dv3.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv3.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv3);
		
		List<String> dv4 = new ArrayList<String>();
		position = new CellSpaceInformation("Table1",0,4);
		dv4.add(manager.getBlocksForPosition(position).get(0).getValueInterpretation(spreadsheet.get(position).getValue()) );
		dv4.add(manager.getBlocksForPosition(positionTotal).get(0).getValueInterpretation(spreadsheet.get(positionTotal).getValue()) );
		domainValues.add(dv4);
		
		Map<Integer, String> constantArgs = Util.getConstantArguments(domainValues);
		assertEquals(new Integer(1), new Integer(constantArgs.size()));
		assertEquals("<ci>Total Costs</ci>", constantArgs.get(1));
		//for (Integer i : constantArgs.keySet())
			//System.out.println("Constant: " + i + " -> " + constantArgs.get(i));
	}
	
	@Test
	public void testConvertCellPosition() {
		assertEquals(new CellSpaceInformation(1,0), Util.convertCellPosition("A2"));
		assertEquals(new CellSpaceInformation(0,1), Util.convertCellPosition("B1"));
	}
	
	@Test
	public void testTagAsMathObject() {
		assertEquals("<math xmlns=\"http://www.w3.org/1998/Math/MathML\">\n  <apply>test</apply>\n</math>\n", Util.tagAsMathMLObject("  <apply>test</apply>\n",mlBuilder));
	}
	
	@Test
	public void testUntagMathObject() {
		assertEquals("  <apply>test</apply>\n", Util.untagMathObject(Util.tagAsMathMLObject("  <apply>test</apply>\n",mlBuilder),mlBuilder));
	}
	
	@Test
	public void testGetCDFromURI() {
		assertEquals("expenses", Util.getCDFromURI("expenses#ExpensesPerYear"));
	}
	
	@Test
	public void testGetSymbolFromURI() {
		assertEquals("ExpensesPerYear", Util.getSymbolFromURI("expenses#ExpensesPerYear"));
	}
	
	@Test
	public void testReplaceURIsWithIdentifiers() {
		assertEquals("Test1 winograd~years spsht-arith~equal Text winograd~ExpensesPerYear More", Util.replaceURIsWithIdentifiers("Test1 winograd#years spsht-arith#equal Text winograd#ExpensesPerYear More"));
	}

}
