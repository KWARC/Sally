package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;

import java.util.List;

import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

public class VerifierTest {
	ModelManager modelManager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	Verifier verifier;
	
	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		modelManager = winData.getModelManager();
		spreadsheet = winData.getSpreadsheet();
		
		verifier = new Verifier(winData.getManager());
	}

	@Test
	public void testCheckValue() {
		assertEquals(VerificationStatus.VERIFIED, verifier.checkValue(new CellSpaceInformation("Table1",4,1)) ) ;
		spreadsheet.get(new CellSpaceInformation("Table1",4,1)).setValue("0.0001");		// Value is to low (0.0001 * 1000000 < 100000)
		try {
			verifier.reinit();
	    } catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
		assertEquals(VerificationStatus.FAILED, verifier.checkValue(new CellSpaceInformation("Table1",4,1)) );
	}

	@Test
	public void testCheckAllValues() {
		assertEquals(VerificationStatus.VERIFIED, verifier.checkAllValues() ) ;
		spreadsheet.get(new CellSpaceInformation("Table1",4,1)).setValue("0.0001");		// Constrains for expenses do not hold any more
		try {
			verifier.reinit();
	    } catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
		assertEquals(VerificationStatus.FAILED, verifier.checkAllValues() ) ;
	}

	@Test
	public void testCheckCPSimilarBlock() throws ModelException {
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(winData.getManager());
		for (CPSimilarBlockData block : cpBlocks)
			assertEquals(VerificationStatus.VERIFIED, verifier.checkCPSimilarBlock(block) ) ;
	}

	@Test
	public void testCheckFunction() {
		try {
			assertEquals(VerificationStatus.VERIFIED, verifier.checkFunction(new CellSpaceInformation("Table1",5,2), winData.getRelationProfit()));
			spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2-C4");
			verifier.reinit();
			assertEquals(VerificationStatus.FAILED, verifier.checkFunction(new CellSpaceInformation("Table1",5,2), winData.getRelationProfit()));
		} catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
	}
	
	@Ignore
	public void testCheckAllFunctions()  {
		try {
			assertEquals(VerificationStatus.VERIFIED, verifier.checkAllFunctions());
			spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2+C5");
			verifier.reinit();
			assertEquals(VerificationStatus.FAILED, verifier.checkAllFunctions());
		} catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
	}

	@Test
	public void testCheckRelation() {
		/*Relation profitRel = winData.getRelationProfit();
		assertEquals(VerificationStatus.SAT, verifier.checkRelation(profitRel));
		spreadsheet.get(new CellSpaceInformation("Table1",4,2)).setFormula("C2+C4");	// Wrong formula in different relation
		verifier.reinit();
		assertEquals(VerificationStatus.SAT, verifier.checkRelation(profitRel));
		spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2+C5");	// Wrong formula in profit relation
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkRelation(profitRel));*/
		try {
			assertEquals(VerificationStatus.VERIFIED, verifier.checkRelation(winData.getRelationTotalCosts()));
			spreadsheet.get(new CellSpaceInformation("Table1",4,2)).setFormula("C3+B4");
			verifier.reinit();
			assertEquals(VerificationStatus.FAILED, verifier.checkRelation(winData.getRelationTotalCosts()));
		} catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
		//verifier.printDebugOutput();
	}
	
}
