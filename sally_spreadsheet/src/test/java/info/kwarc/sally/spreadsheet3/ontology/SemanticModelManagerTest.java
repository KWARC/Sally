package info.kwarc.sally.spreadsheet3.ontology;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Message;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import org.junit.Before;
import org.junit.Test;

public class SemanticModelManagerTest {
	ModelManager manager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	SemanticModelManager semanticModel;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		winData.createSecondWorksheet();
		manager = winData.getModelManager();
		spreadsheet = winData.getSpreadsheet();
		
		semanticModel = new SemanticModelManager();
		semanticModel.createSemanticValues(manager.getRelationsFor(null, null, Relation.RelationType.TYPERELATION), spreadsheet);
	}

	@Test
	public void testCheckBlockForCompleteness() throws ModelException {
		assertEquals(Message.MessageSubType.Succeed, semanticModel.checkBlockForCompleteness(winData.getYear(), winData.getTypeYear().getUri(), spreadsheet).getSubType());
		assertEquals(Message.MessageSubType.Succeed, semanticModel.checkBlockForCompleteness(winData.getCost(), winData.getTypeCost().getUri(), spreadsheet).getSubType());
		
		// ERROR because DataCosts is should not be complete (No property COMPLETESEMANTICBLOCK = true)
		Message msg = semanticModel.checkBlockForCompleteness(winData.getDataCosts(), winData.getTypeDataCosts().getUri(), spreadsheet);
		assertEquals(Message.MessageSubType.Info, msg.getSubType());
		assertEquals("Unchecked block", msg.getMessage());
		
		// year2 is incomplete because 1987 is missing.
		assertEquals(Message.MessageSubType.SemanticIncomplete, semanticModel.checkBlockForCompleteness(winData.getYear2(), winData.getTypeYear2().getUri(), spreadsheet).getSubType());
	}

}
