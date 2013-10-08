package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;

import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
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
		Map<Block, String> blocksToUris = new HashMap<Block,String>();
		for (Block b : winData.getManager().getAllTopLevelBlocks())
			blocksToUris.put(b, "TODO");
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(blocksToUris, winData.getSpreadsheet());
		assertEquals("<ci>Costtype: Revenues</ci>", dataTypes.get("omdoc://winograd#Costs").get(0));
		assertEquals("<apply><csymbol>times</csymbol><ci>1000000</ci><ci>0.2</ci></apply>", dataTypes.get("omdoc://winograd#CostsPerYear").get(5));
	}
	
	@Test
	public void extractCPSimilarFBsTest() {
		//VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet());
		List <String> cpSimilarRepresentations = new ArrayList<String>(VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(2, cpSimilarRepresentations.size());
		System.out.println("CPSimilar:\n" + cpSimilarRepresentations.get(0));
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
				"</apply>\n",cpSimilarRepresentations.get(0).replaceAll("\r", "")
				);
	}
	
	@Test
	public void extractMLFormulaRepresentationsTest() {
		List <String> mlFormulae = new ArrayList<String>(VerificationDataExtractor.extractMLFormulaRepresentations(winData.getRelationCalc(), winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(4, mlFormulae.size());
		System.out.println("Formula for 1986:\n" + Util.tagAsMathMLObject(mlFormulae.get(2), new BuilderMathML()) );

	}

}
