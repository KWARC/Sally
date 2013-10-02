package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.ArrayList;
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
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(winData.getManager().getAllTopLevelBlocks(), winData.getSpreadsheet());
		assertEquals("<ci>Costtype: Revenues</ci>", dataTypes.get("omdoc://winograd#Costs").get(0));
		assertEquals("<apply><csymbol>times</csymbol><ci>1000000</ci><ci>0.2</ci></apply>", dataTypes.get("omdoc://winograd#CostsPerYear").get(5));
	}
	
	@Test
	public void extractCPSimilarFBsTest() {
		//VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet());
		List <String> cpSimilarRepresentations = new ArrayList<String>(VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet(), builderML).values());
		assertEquals(1, cpSimilarRepresentations.size());
		assertEquals(
				"<apply>\n" +
				"<csymbol cd=\"spsht-arith\">equal</csymbol>\n" +
				"<apply>\n" +
				"<csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				"<ci>?X0</ci>\n" +
				"<ci>?X1</ci>\n" +
				"</apply>\n" +
				"  <apply>\n" +
				"    <csymbol cd=\"spsht-arith\">plus</csymbol>\n" +
				"      <apply><csymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>?X0</ci><ci>Costtype: Revenues</ci></apply>\n" +
				"      <apply><csymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>?X0</ci><ci>Costtype: Materials</ci></apply>\n" +
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
