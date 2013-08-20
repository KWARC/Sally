package info.kwarc.sally.spreadsheet2;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import sally.CreateBlockRange;
import sally.GetBlocksInRange;
import sally.IDList;

public class ASMInterfaceTest {
	ASMInterface asm;
	sally.IDMessage yearID, costsID, dataID, relationID;

	@Before
	public void setUp() throws Exception {
		asm = new ASMInterface();
		
		asm.createBlockRange(CreateBlockRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",0,1,0,4))).build());
		yearID = asm.getBlocksInRange(GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",0,1,0,4))).build()).getIdListList().get(0);
		sally.ValueInterpretation viYear = sally.ValueInterpretation.newBuilder()
			.setPatternString("#1")
			.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
					sally.IntegerStringPair.newBuilder().setId(1).setValue("\\d+").build()).build())
			.setInterpretationTemplate("<ci>Year #1 AD</ci>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(yearID.getId()).setUri("Years").addValueInterpretations(viYear).build());
		
		
		asm.createBlockRange(CreateBlockRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,0,4,0))).build());
		costsID = asm.getBlocksInRange(GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,0,4,0))).build()).getIdListList().get(0);
		sally.ValueInterpretation viCosts = sally.ValueInterpretation.newBuilder()
				.setPatternString("#1")
				.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
						sally.IntegerStringPair.newBuilder().setId(1).setValue( "\\p{Alpha}+").build()).build())
				.setInterpretationTemplate("<ci>Costtype: #1</ci>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(costsID.getId()).setUri("Costs").addValueInterpretations(viCosts).build());
		
		asm.createBlockRange(CreateBlockRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,1,4,4))).build());
		dataID = asm.getBlocksInRange(GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",1,1,4,4))).build()).getIdListList().get(0);
		sally.ValueInterpretation viData = sally.ValueInterpretation.newBuilder()
				.setPatternString("#1")
				.setSubExpressions(sally.IntegerStringMapping.newBuilder().addPair(
						sally.IntegerStringPair.newBuilder().setId(1).setValue( "\\d+").build()).build())
				.setInterpretationTemplate("<apply><csymbol>times</csymbol><ci>1000000</ci><ci>#1</ci></apply>").build();
		asm.createOntologyBlockLink(sally.CreateOntologyBlockLink.newBuilder().setBlockId(dataID.getId()).setUri("ExpensesPerYearData").addValueInterpretations(viData).build());
		
		asm.createFunctionalRelation(sally.CreateFunctionalRelation.newBuilder().setBlockIds(sally.IDList.newBuilder().addIdList(yearID).addIdList(costsID).addIdList(dataID).build()).build());
		relationID = asm.getRelationsForPosition(sally.GetRelationsForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",1,1,4,4))).build()).getIdListList().get(0);
		asm.createOntologyRelationLink(sally.CreateOntologyRelationLink.newBuilder().setId(relationID.getId()).setUri("ExpensesPerYear")
				.setMathMLTemplate("<apply><cymbol cd=\"LocalDomain\">Expenses per Year</csymbol><rvar num=\"1\"/><rvar num=\"2\"/></apply>")
				.setBlockIds(sally.IDList.newBuilder().addIdList(yearID).addIdList(costsID).build()).build());
	}

	@Test
	public void testGetBlocksForPosition() {
		IDList result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,2))).build());
		assertEquals(1,result.getIdListCount());
		assertEquals(yearID, result.getIdList(0));
		result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,0))).build());
		assertEquals(1,result.getIdListCount());
		assertEquals(costsID, result.getIdList(0));
		result = asm.getBlocksForPosition(sally.GetBlocksForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",2,2))).build());
		assertEquals(1,result.getIdListCount());
		assertEquals(dataID, result.getIdList(0));
	}

	@Test
	public void testGetBlocksInRange() {
		IDList result = asm.getBlocksInRange(sally.GetBlocksInRange.newBuilder().setRange(MessageConverter.RangeInformationToCellRangePosition(new RangeInformation("Table1",2,0,3,4))).build());
		assertEquals(2, result.getIdListCount());
		assertTrue(result.getIdListList().contains(costsID));
		assertTrue(result.getIdListList().contains(dataID));
	}

	@Test
	public void testGetAllPositionsOfBlock() {
		sally.CellPositions2 positions = asm.getAllPositionsOfBlock(sally.GetAllPositionsOfBlock.newBuilder().setId(yearID).build());
		assertEquals(4, positions.getCellPositionsCount());
		assertTrue(positions.getCellPositionsList().contains(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,3))));
	}

	@Test
	public void testGetRelationsForPosition() {
		IDList relation = asm.getRelationsForPosition(sally.GetRelationsForPosition.newBuilder().setPosition(MessageConverter.cellSpaceInformationToCellPosition(new CellSpaceInformation("Table1",0,3))).build());
		assertEquals(1, relation.getIdListCount());
		assertEquals(1, relation.getIdList(0).getId());
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
