package info.kwarc.sally.spreadsheet3.ontology;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import org.junit.Before;
import org.junit.Test;

public class SemanticModelManagerTest {
	Manager manager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	SemanticModelManager semanticModel;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		winData.createSecondWorksheet();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
		
		semanticModel = new SemanticModelManager();
		semanticModel.createSemanticValues(manager.getRelationsFor(null, null, Relation.RelationType.TYPERELATION), spreadsheet);
	}

	@Test
	public void testCheckBlockForCompleteness() {
		assertEquals(SemanticModelMessage.MessageType.VALID, semanticModel.checkBlockForCompleteness(winData.getYear(), winData.getTypeYear().getUri(), spreadsheet).getType());
		assertEquals(SemanticModelMessage.MessageType.VALID, semanticModel.checkBlockForCompleteness(winData.getCost(), winData.getTypeCost().getUri(), spreadsheet).getType());
		
		// ERROR because DataCosts is should not be complete (No property COMPLETESEMANTICBLOCK = true)
		assertEquals(SemanticModelMessage.MessageType.UNCHECKED, semanticModel.checkBlockForCompleteness(winData.getDataCosts(), winData.getTypeDataCosts().getUri(), spreadsheet).getType());
		
		// year2 is incomplete because 1987 is missing.
		assertEquals(SemanticModelMessage.MessageType.INCOMPLETEBLOCK, semanticModel.checkBlockForCompleteness(winData.getYear2(), winData.getTypeYear2().getUri(), spreadsheet).getType());
	}

}
