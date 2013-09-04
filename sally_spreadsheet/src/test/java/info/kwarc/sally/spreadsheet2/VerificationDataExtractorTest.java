package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class VerificationDataExtractorTest {
	WinogradData winData;

	@Before
	public void setUp() throws Exception {
		winData =  new WinogradData();
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
		List <String> cpSimilarRepresentations = VerificationDataExtractor.extractCPSimilarFBs(winData.getManager(), winData.getSpreadsheet());
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
				"    <apply>\n" +
				"      <csymbol cd=\"spshform\">semanticObject</csymbol>\n" +
				"      <apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>?X0</ci><ci>Costtype: Revenues</ci></apply>\n" +
				"    </apply>\n" +
				"    <apply>\n" +
				"      <csymbol cd=\"spshform\">semanticObject</csymbol>\n" +
				"      <apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>?X0</ci><ci>Costtype: Materials</ci></apply>\n" +
				"    </apply>\n" +
				"  </apply>\n",cpSimilarRepresentations.get(0).replaceAll("\r", "")
				);
	}

}