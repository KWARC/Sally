package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

/**
 * Testing the ASMInterface by modeling a simplification of the Winograd spreadsheet. 
 * @author cliguda
 * Note: The value-interpretation uses some pseudo-MathML template for testing, but every MathML can be used. 
 */

public class ASMInterfaceTest {
	ASMInterface asm;
	Integer yearID, costsID, dataID, relationID;

	@Before
	public void setUp() throws Exception {
		asm = new ASMInterface();
		
		asm.createBlockRange(sally.CreateBlockForRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",0,1,0,4))).build());
		yearID = asm.getBlocksInRange(sally.GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",0,1,0,4))).build()).getIdsList().get(0);
		// Value interpretation: #1 -> <ci>Year #1 AD</ci>, e.g. 1984 -> <ci>Year 1984 AD</ci>
		sally.ValueInterpretation viYear = sally.ValueInterpretation.newBuilder()
			.setPatternString("#1")
			.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
					sally.IntegerStringPair.newBuilder().setId(1).setValue("\\d+").build()).build())
			.setInterpretationTemplate("<ci>Year <rvar num=\"1\"/> AD</ci>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(yearID).setUri("Years").addValueInterpretations(viYear).build());
		
		asm.createBlockRange(sally.CreateBlockForRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,0,4,0))).build());
		costsID = asm.getBlocksInRange(sally.GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,0,4,0))).build()).getIdsList().get(0);
		// Value interpretation: #1 -> <ci>Costtype: #1</ci>, e.g. Sallaries -> <ci>Costtype: Sallaries</ci>
		sally.ValueInterpretation viCosts = sally.ValueInterpretation.newBuilder()
				.setPatternString("#1")
				.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
						sally.IntegerStringPair.newBuilder().setId(1).setValue( "\\p{Alpha}+").build()).build())
				.setInterpretationTemplate("<ci>Costtype: <rvar num=\"1\"/></ci>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(costsID).setUri("Costs").addValueInterpretations(viCosts).build());
		
		asm.createBlockRange(sally.CreateBlockForRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,1,4,4))).build());
		dataID = asm.getBlocksInRange(sally.GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,1,4,4))).build()).getIdsList().get(0);
		// Value interpretation: #1 -> <apply><csymbol>times</csymbol><ci>1000000</ci><ci>#1</ci></apply>, e.g. 53 -> <apply><csymbol>times</csymbol><ci>1000000</ci><ci>53</ci></apply>
		sally.ValueInterpretation viData = sally.ValueInterpretation.newBuilder()
				.setPatternString("#1")
				.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
						sally.IntegerStringPair.newBuilder().setId(1).setValue( "\\d+").build()).build())
				.setInterpretationTemplate("<apply><csymbol>times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(dataID).setUri("ExpensesPerYearData").addValueInterpretations(viData).build());
		
		asm.createFunctionalRelation(sally.CreateFunctionalRelation.newBuilder().addBlockIds(yearID).addBlockIds(costsID).addBlockIds(dataID).build());
		relationID = asm.getRelationsForPosition(sally.GetRelationsForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",1,1,4,4))).build()).getIdsList().get(0);
		// Function interpretation example: The cell that represents the salaries for 1984 can be interpreted as: 
		// <apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Salaries</ci></apply>
		asm.createOntologyRelationLink(sally.CreateOntologyRelationLink.newBuilder().setId(relationID).setUri("ExpensesPerYear")
				.setMathMLTemplate("<apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><rvar num=\"1\"/><rvar num=\"2\"/></apply>")
				.addBlockIds(yearID).addBlockIds(costsID).build());
	}

	@Test
	public void testGetBlocksForPosition() {
		sally.IDList result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,2))).build());
		assertEquals(1,result.getIdsCount());
		assertTrue(yearID == result.getIds(0));
		result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,0))).build());
		assertEquals(1,result.getIdsCount());
		assertTrue(costsID == result.getIds(0));
		result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,2))).build());
		assertEquals(1,result.getIdsCount());
		assertTrue(dataID == result.getIds(0));
	}

	@Test
	public void testGetBlocksInRange() {
		sally.IDList result = asm.getBlocksInRange(sally.GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",2,0,3,4))).build());
		assertEquals(2, result.getIdsCount());
		assertTrue(result.getIdsList().contains(costsID));
		assertTrue(result.getIdsList().contains(dataID));
	}

	@Test
	public void testGetAllPositionsOfBlock() {
		sally.CellPositions2 positions = asm.getAllPositionsOfBlock(sally.GetAllPositionsOfBlock.newBuilder().setId(yearID).build());
		assertEquals(4, positions.getCellPositionsCount());
		assertTrue(positions.getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,3))));
	}

	@Test
	public void testGetRelationsForPosition() {
		sally.IDList relation = asm.getRelationsForPosition(sally.GetRelationsForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,3))).build());
		assertEquals(1, relation.getIdsCount());
		assertEquals(1, relation.getIds(0));
	}

	@Test
	public void testGetCellRelationsForPosition() {
		sally.CellPositionsList2 tupleList = asm.getCellRelationsForPosition(sally.GetCellRelationsForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,3))).build());
		assertEquals(1, tupleList.getCellPositionsListCount());
		assertEquals(3, tupleList.getCellPositionsList(0).getCellPositionsCount());
		assertTrue(tupleList.getCellPositionsList(0).getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,3))));
		assertTrue(tupleList.getCellPositionsList(0).getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,0))));
		assertTrue(tupleList.getCellPositionsList(0).getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,3))));
		assertFalse(tupleList.getCellPositionsList(0).getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,2))));
	}

	@Test
	public void testGetUriForBlock() {
		assertEquals("Years", asm.getUriForBlock(sally.GetUriForBlock.newBuilder().setBlockID(yearID).build()).getData());
		assertEquals("Costs", asm.getUriForBlock(sally.GetUriForBlock.newBuilder().setBlockID(costsID).build()).getData());
		assertEquals("ExpensesPerYearData", asm.getUriForBlock(sally.GetUriForBlock.newBuilder().setBlockID(dataID).build()).getData());
	}
	
	@Test
	public void testGetUriForRelation() {
		assertEquals("ExpensesPerYear", asm.getUriForRelation(sally.GetUriForRelation.newBuilder().setRelationID(relationID).build()).getData());
	}

	@Test
	public void testGetValueInterpretation() {
		assertEquals("<ci>Year 1984 AD</ci>", asm.getValueInterpretation(sally.GetValueInterpretation.newBuilder().setBlockID(yearID).setValue("1984").build()).getData());
		assertEquals("<ci>Costtype: Salaries</ci>", asm.getValueInterpretation(sally.GetValueInterpretation.newBuilder().setBlockID(costsID).setValue("Salaries").build()).getData());
		assertEquals("<apply><csymbol>times</csymbol><ci>1000000</ci><ci>123</ci></apply>", asm.getValueInterpretation(sally.GetValueInterpretation.newBuilder().setBlockID(dataID).setValue("123").build()).getData());
	}

	@Test
	public void testGetIntendedFunctionForValues() {
		assertEquals("<apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Salaries</ci></apply>", asm.getIntendedFunctionForValues(sally.GetIntendedFunctionForValues.newBuilder().setRelationID(relationID).addValues("1984").addValues("Salaries").build()).getData());
	}

}
