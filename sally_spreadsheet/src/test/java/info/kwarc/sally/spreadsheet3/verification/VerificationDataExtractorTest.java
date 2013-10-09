package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;

import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
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

	@Before
	public void setUp() throws Exception {
		winData =  new WinogradData();
		builderML = new BuilderMathML();
	}

	@Test
	public void extractDataTypesTest() {
		Map<Block, String> blocksToUris = new HashMap<Block, String>();
		for (Block b : winData.getManager().getAllTopLevelBlocks()) {
			Relation blockRelation = winData.getManager().getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			
			blocksToUris.put(b, blockRelation.getUri());	
		}
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(blocksToUris, winData.getSpreadsheet());
		
		assertEquals("<ci>Year 1985 AD</ci>", dataTypes.get("omdoc://winograd#Year").get(1));
		assertEquals("<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci>0.3</ci></apply>", dataTypes.get("omdoc://winograd#Money").get(2));
	}
	
	@Test
	public void extractCPSimilarFBsTest() {
		List <String> cpSimilarRepresentations = new ArrayList<String>(VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(2, cpSimilarRepresentations.size());
		int indexExpensesPerYear = 0;
		if (cpSimilarRepresentations.get(0).contains("profit"))
			indexExpensesPerYear = 1;		// Sometimes the order flips
		assertEquals(
				"<apply>\n" +
				"<csymbol cd=\"spsht-arith\">equal</csymbol>\n" +
				"<apply>\n" +
				"<csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"<rvar num=\"0\"/>\n" +
				"<rvar num=\"1\"/>\n" +
				"</apply>\n" +
				"  <apply>\n" +
				"    <csymbol cd=\"spsht-arith\">plus</csymbol>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"      <rvar num=\"0\"/>\n" +
				"      <ci>Costtype: Materials</ci>\n" +
				"      </apply>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"      <rvar num=\"0\"/>\n" +
				"      <ci>Costtype: Salaries</ci>\n" +
				"      </apply>\n" +
				"  </apply>\n" +
				"</apply>\n",cpSimilarRepresentations.get(indexExpensesPerYear).replaceAll("\r", "")
				);
	}
	
	@Test
	public void extractMLFormulaRepresentationsTest() {
		List <String> mlFormulae = new ArrayList<String>(VerificationDataExtractor.extractMLFormulaRepresentations(winData.getRelationCalc(), winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(4, mlFormulae.size());
		assertEquals(
				"<math xmlns=\"http://www.w3.org/1998/Math/MathML\">\n" +
				"<apply>\n" +
				"<csymbol cd=\"spsht-arith\">equal</csymbol>\n" +
				"<apply>\n" +
				"<csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"<ci>Year 1986 AD</ci>\n" +
				"<ci>Costtype: total</ci>\n" +
				"</apply>\n" +
				"  <apply>\n" +
				"    <csymbol cd=\"spsht-arith\">plus</csymbol>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"      <ci>Year 1986 AD</ci>\n" +
				"      <ci>Costtype: Materials</ci>\n" +
				"      </apply>\n" +
				"      <apply>\n" +
				"      <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"      <ci>Year 1986 AD</ci>\n" +
				"      <ci>Costtype: Salaries</ci>\n" +
				"      </apply>\n" +
				"  </apply>\n" +
				"</apply>\n" +
				"</math>\n", Util.tagAsMathMLObject(mlFormulae.get(2), new BuilderMathML()).replaceAll("\r", ""));
	}

}
