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
		assertEquals("<ci>Costtype: Revenues</ci>", dataTypes.get("Costs").get(0));
		assertEquals("<apply><csymbol>times</csymbol><ci>1000000</ci><ci>1.1</ci></apply>", dataTypes.get("CostsPerYear").get(4));
	}

}
