package info.kwarc.sally.spreadsheet3.ontology;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

public class BuilderMathMLTest {
	BuilderMathML builder;

	@Before
	public void setUp() throws Exception {
		builder = new BuilderMathML();
	}
	
	@Test
	public void testParseMLAxiom() throws OntologyException {
		AxiomObject axiom = builder.parseMLAxiom("test",
				  "<apply>"
				+ "<forall/>"
				+ "<bvar><ci> n </ci></bvar>"
				+ "<condition>"
				+ "<apply><and/>"
				+ "<apply><gt/><ci> n </ci><cn> 0 </cn></apply>"
				+ "<apply><in/><ci> n </ci><ci>Integer</ci></apply>"
				+ "</apply>"
				+ "</condition>"
				+ "<apply>"
				+ "<exists/>"
				+ "<bvar><ci> x </ci></bvar>"
				+ "<bvar><ci> y </ci></bvar>"
				+ "<bvar><ci> z </ci></bvar>"
				+ "<condition>"
				+ "<apply><and/>"
				+ "<apply><in/><ci> x </ci><ci>Integer</ci></apply>"
				+ "<apply><in/><ci> y </ci><ci>Integer</ci></apply>"
				+ "<apply><in/><ci> z </ci><ci>Integer</ci></apply>"
				+ "</apply>"
				+ "</condition>"
				+ "<apply>"
				+ "<eq/>"
				+ "<apply>"
				+ "<plus/>"
				+ "<apply><power/><ci> x </ci><ci> n </ci></apply>"
				+ "<apply><power/><ci> y </ci><ci> n </ci></apply>"
				+ "</apply>"
				+ "<apply><power/><ci> z </ci><ci> n </ci></apply>"
				+ "</apply>"
				+ "</apply>"
				+ "</apply>");
		assertTrue(axiom.getVariables().size() == 4);
		AxiomVariableObject var = axiom.getVariables().get(0);
		assertEquals("n", var.getName());
		assertEquals("Integer", var.getType());
		assertEquals(AxiomVariableObject.QuantorType.All, var.getQuantorType());
		assertEquals("<apply><gt/><ci> n </ci><cn> 0 </cn></apply>", axiom.getVarConditions());
		assertEquals("<apply><eq/><apply><plus/><apply><power/><ci> x </ci><ci> n </ci></apply><apply><power/><ci> y </ci><ci> n </ci></apply></apply><apply><power/><ci> z </ci><ci> n </ci></apply></apply>" 
				, axiom.getMLConstrain());
	}

}
