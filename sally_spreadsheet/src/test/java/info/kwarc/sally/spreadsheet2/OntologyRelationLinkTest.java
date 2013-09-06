package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class OntologyRelationLinkTest {
	
	OntologyRelationLink relationLink;
	BuilderML builderML;

	@Before
	public void setUp() throws Exception {
		List<OntologyBlockLink> blockLinks = new ArrayList<OntologyBlockLink>();
		builderML = new BuilderMathML();
		
		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		ValueInterpretation vi = new ValueInterpretation("#1", subExpressions, "<ci>Year <rvar num=\"1\"/> AD</ci>", builderML);
		blockLinks.add(new OntologyBlockLink("omdoc://winograd#Years", vi));
		
		Map<Integer, String> subExpressions2 = new HashMap<Integer,String>();
		subExpressions2.put(new Integer(1), "\\p{Alpha}+");
		ValueInterpretation vi2 = new ValueInterpretation("#1", subExpressions2, "<ci>Costtype: <rvar num=\"1\"/></ci>", builderML);
		blockLinks.add(new OntologyBlockLink("omdoc://winograd#Costs", vi2));
		relationLink = new OntologyRelationLink("omdoc://winograd#ExpensesPerYear",
				"<apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><rvar num=\"1\"/><rvar num=\"2\"/></apply>", blockLinks, builderML);
	}

	@Test
	public void testGetRelationInterpretation() {
		List<String> parameters = new ArrayList<String>();
		parameters.add("1984");
		parameters.add("Salaries");
		assertEquals("<apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Salaries</ci></apply>", relationLink.getRelationInterpretation(parameters));
	}
	
	

}
