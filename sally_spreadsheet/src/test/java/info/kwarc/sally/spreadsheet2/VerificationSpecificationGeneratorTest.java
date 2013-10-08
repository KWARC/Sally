package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

public class VerificationSpecificationGeneratorTest {
	Manager manager;
	FormalSpreadsheet spreadsheet;

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
	}

	@Ignore
	public void testGetDataTypeSpecification() {
		// Datatypes
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(manager.getAllTopLevelBlocks(), spreadsheet);
		List<String> dtSpec = VerificationSpecificationGenerator.getDataTypeSpecification(dataTypes).getSpecification();
		System.out.println("Datatypes:");
		for (String s : dtSpec)
			System.out.println(s);
	}

	@Ignore
	public void testGetFunctionDefinition() {
		fail("Not yet implemented");
	}

	@Ignore
	public void testCreateFunctionDeclarations() {
		System.out.println("Function declarations:");
		for (String decl : VerificationSpecificationGenerator.createFunctionDeclarations((new OntologyData()).getAll()))
			System.out.println(decl);
	}

	@Ignore
	public void testCreateFunctionDefinitions() {
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(manager.getAllTopLevelBlocks(), spreadsheet);
		DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(dataTypes);
		System.out.println("Function definitions:");
		for (String def : VerificationSpecificationGenerator.createFunctionDefinitions( (new OntologyData()).getAll(), dataTypesSpec.getIdentifierToSymbol()))
			System.out.println(def);
	}
	
	@Test
	public void testCreateAxiom() {
		String axiom = "<apply><forall/><bvar><ci>y</ci></bvar><condition><apply><and/><apply><in/><ci>y</ci><ci>omdoc://winograd#years</ci></apply></apply></condition>" +
			"<apply><csymbol cd=\"spsht-arith\">equal</csymbol><apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Costtype: total</ci><ci>y</ci></apply> " +
			"<apply><csymbol cd=\"spsht-arith\">sum5</csymbol>" +
			"<apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Costtype: Salaries</ci><ci>y</ci></apply>" +
			"<apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Costtype: Materials</ci><ci>y</ci></apply>" +
			"<apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Costtype: Revenues</ci><ci>y</ci></apply>" +
			"</apply></apply></apply>";
		System.out.println("Axiom:");
		System.out.println(VerificationSpecificationGenerator.getAxiom(axiom));
	}

	@Ignore
	public void testCreateCompeteSpecification() {
		fail("Not yet implemented");
	}

}
