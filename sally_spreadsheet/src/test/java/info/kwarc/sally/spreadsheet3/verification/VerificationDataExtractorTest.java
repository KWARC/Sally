package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathML;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class VerificationDataExtractorTest {
	WinogradData winData;
	BuilderML builderML;
	//List<String> standardTypes;

	@Before
	public void setUp() throws Exception {
		winData =  new WinogradData();
		builderML = new BuilderMathML();
		/*standardTypes = new ArrayList<String>();
		standardTypes.add("money#monetary-quantity");
		standardTypes.add("spsht-numbers#spshReal");
		standardTypes.add("spsht-bool#spshBool");*/
	}

	@Test
	public void extractDataTypesTest() {
		Map<Block, String> blocksToUris = new HashMap<Block, String>();
		for (Block b : winData.getManager().getAllTopLevelBlocks()) {
			Relation blockRelation = winData.getManager().getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			
			blocksToUris.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocksToUris, winData.getSpreadsheet());
		
		assertTrue(dataTypes.size() == 29);
		assertEquals("profits#profit", dataTypes.get(0).getOntologyType());
		assertEquals("<ci>Profit</ci>", dataTypes.get(0).getContent());
		assertEquals(new CellSpaceInformation("Table1",5,0), dataTypes.get(0).getPostition());
	}
	
	@Test
	public void extractCPSimilarFBsTest() {
		List<CPSimilarBlockData> cpSimilarRepresentations = new ArrayList<CPSimilarBlockData>(VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet(), builderML));
		assertEquals(2, cpSimilarRepresentations.size());
		int indexExpensesPerYear = 0;
		if (cpSimilarRepresentations.get(0).getAntiunification().contains("profit"))
			indexExpensesPerYear = 1;		// Sometimes the order flips
		assertEquals(
				"<apply>\n" +
				"<csymbol cd=\"spsht-arith\">equal</csymbol>\n" +
				"<apply>\n" +
				"<csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"<rvar num=\"0\"/>\n" +
				"<rvar num=\"1\"/>\n" +
				"</apply>\n" +
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
				"</apply>\n",cpSimilarRepresentations.get(indexExpensesPerYear).getAntiunification().replaceAll("\r", "")
				);
	}
	
	@Test
	public void extractMLFormulaRepresentationsTest() {
		List <String> mlFormulae = new ArrayList<String>(VerificationDataExtractor.extractMLFormulaRepresentations(winData.getRelationTotalCosts(), winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(4, mlFormulae.size());
		assertEquals(
				"<math xmlns=\"http://www.w3.org/1998/Math/MathML\">\n" +
				"<apply>\n" +
				"<csymbol cd=\"spsht-arith\">equal</csymbol>\n" +
				"<apply>\n" +
				"<csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"<ci>Year 1986 AD</ci>\n" +
				"<ci>Total Costs</ci>\n" +
				"</apply>\n" +
				"  <apply>\n" +
				"    <csymbol cd=\"spsht-arith\">plus</csymbol>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"      <ci>Year 1986 AD</ci>\n" +
				"      <ci>Material Costs</ci>\n" +
				"      </apply>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				"      <ci>Year 1986 AD</ci>\n" +
				"      <ci>Salary Costs</ci>\n" +
				"      </apply>\n" +
				"  </apply>\n" +
				"</apply>\n" +
				"</math>\n", Util.tagAsMathMLObject(mlFormulae.get(2), new BuilderMathML()).replaceAll("\r", ""));
	}

}
