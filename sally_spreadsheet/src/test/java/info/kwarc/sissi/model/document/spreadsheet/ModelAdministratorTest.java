package info.kwarc.sissi.model.document.spreadsheet;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class ModelAdministratorTest {
	ModelAdministrator asm;

	@Before
	public void setUp() throws Exception {
		asm = new ModelAdministrator();
		for (CellSpaceInformation pos : WinogradData.getFormalWinograd().getAllPositions())
			asm.setContent(pos, WinogradData.getFormalWinograd().getContent(pos).getValue() , "");
	}

	@Test
	public void testCreateLegend() {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<Legend> legends = asm.getAllLegends();
		assertEquals("size", 1, legends.size());
		Legend l = legends.get(0);
		assertEquals("Item 1", "1984", l.getItems().get(0).getValue());
		assertEquals("Item 2", "1985", l.getItems().get(1).getValue());
		assertEquals("Item 3", "1986", l.getItems().get(2).getValue());
		assertEquals("Item 4", "1987", l.getItems().get(3).getValue());	
	}

	@Test
	public void testCreateAbstractElement() {
		AbstractSsElement e = asm.createAbstractElement(new CellSpaceInformation(0,0,1));
		assertEquals("Value", "Actual", e.getValue());
		assertEquals("ValueType", ContentValueType.STRING_NUMBER, e.getValueType());
		assertEquals("Parameters", 0, e.getParameters().size());
	}

	@Test
	public void testCreateLegendProductEntry() {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positions,StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> positionsCosts = new ArrayList<CellSpaceInformation>();
		positionsCosts.add(new CellSpaceInformation(0,2,0));
		positionsCosts.add(new CellSpaceInformation(0,3,0));
		positionsCosts.add(new CellSpaceInformation(0,4,0));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsCosts, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> productPos = new ArrayList<CellSpaceInformation>();
		productPos.add(new CellSpaceInformation(0,1,2));
		productPos.add(new CellSpaceInformation(0,3,0));
		
		List<Legend> legends = new ArrayList<Legend>();
		legends.add( asm.getLegendforPosition(productPos.get(0)));
		legends.add( asm.getLegendforPosition(productPos.get(1)));
					
		List<AbstractSsElement> absElements = new ArrayList<AbstractSsElement>();
		for (CellSpaceInformation position : productPos) 
			absElements.add(asm.getElementForPosition(position) );
		LegendProductEntry entry = new LegendProductEntry(legends, absElements);
		
		assertEquals("Legends", legends, entry.getLegends());
		assertEquals("Entry 1", "1985", entry.getLegendTuple().get(0).getValue());
		assertEquals("Entry 2", "c2", entry.getLegendTuple().get(1).getValue());
	}
	
	@Test
	public void testCreateFB() {
		List<Legend> legends = setupLegends();
		LegendProduct legendProduct = new LegendProduct(legends);
		
		List<CellSpaceInformation> fbPositions = asm.filterEmpty(asm.createCellSpaceInformation(
				new CellSpaceInformation(0,2,1), new CellSpaceInformation(0,3,4)));
		
		Map<CellSpaceInformation, AbstractSsElement> elements = asm.createAbstractElements(fbPositions, StructureCreateParameter.DataParameter.SameContentSameElement);
		
		StructureCreateParameter p = new StructureCreateParameter();
		List<Integer> connectToAll = new ArrayList<Integer>();
		connectToAll.add(3);
		p.setConnectToAll(connectToAll);
		
		Map<CellSpaceInformation, LegendProductEntry> domain = asm.createDomainInformation(fbPositions, legends, p);
		
		assertEquals("Element Size", fbPositions.size(), elements.keySet().size());
		assertEquals("Domain Size", fbPositions.size(), domain.keySet().size());
		
		FunctionalBlock fb = asm.createFB(new FunctionalBlockMapping(legendProduct, elements, domain));
		
		assertEquals("FB Test", "1.2", fb.getEntry(domain.get(new CellSpaceInformation(0,3,2))).getValue()  );
		
		AbstractSsElement el = asm.getElementForPosition(new CellSpaceInformation(0,3,2));
		List<LegendProductEntry> entries = fb.getLegendElementsFor(el);
		assertEquals("Number of legend product entries", 1, entries.size());
		assertEquals("Size of the first legend tuple entry.", 4, entries.get(0).getLegendTuple().size());
		assertTrue("Entry in Domain", fb.getDomainLegends().isValidEntry(entries.get(0)));
		assertEquals("Number of cell positions", 4,  asm.getAssociated(entries.get(0), fb.getDomainLegends(), new CellSpaceInformation(0,3,2)).size());
		
		assertEquals("Same abstract element", asm.getElementForPosition(new CellSpaceInformation(0,2,1)), asm.getElementForPosition(new CellSpaceInformation(0,3,1)));
		assertFalse("Same abstract element", asm.getElementForPosition(new CellSpaceInformation(0,2,2)).equals( asm.getElementForPosition(new CellSpaceInformation(0,3,2))) );	
	}

	@Test
	public void testFindAssociatedCells() {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> positionsCosts = new ArrayList<CellSpaceInformation>();
		positionsCosts.add(new CellSpaceInformation(0,2,0));
		positionsCosts.add(new CellSpaceInformation(0,3,0));
		positionsCosts.add(new CellSpaceInformation(0,4,0));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsCosts, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> productPos = new ArrayList<CellSpaceInformation>();
		productPos.add(new CellSpaceInformation(0,1,2));
		productPos.add(new CellSpaceInformation(0,3,0));
		
		List<Legend> legends = new ArrayList<Legend>();
		legends.add(asm.getLegendforPosition(productPos.get(0)));
		legends.add(asm.getLegendforPosition(productPos.get(1)));
		
		Map<Legend, List<CellSpaceInformation>> assocPositions = asm.getAssociatedCells(new CellSpaceInformation(0,5,7), legends);
		for (Legend l : legends)
			assertEquals("Empty Pos", 0, assocPositions.get(l).size());
		
		assocPositions = asm.getAssociatedCells(new CellSpaceInformation(0,2,3), legends);
		
		assertEquals("Assoc Costs", new CellSpaceInformation(0,1,3), assocPositions.get(legends.get(0)).get(0));
		assertEquals("Assoc Costs", new CellSpaceInformation(0,2,0), assocPositions.get(legends.get(1)).get(0));
		
	}
	
	@Test
	public void findSurroundingLegends() {
		List<CellSpaceInformation> years = asm.filterEmpty(asm.createCellSpaceInformation(
				new CellSpaceInformation(0,1,1), new CellSpaceInformation(0,1,4)));
		Legend yearLegend = asm.createLegend(new LegendMapping(asm.createAbstractElements(years, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> costs = asm.filterEmpty(asm.createCellSpaceInformation(
				new CellSpaceInformation(0,2,0), new CellSpaceInformation(0,4,0)));
		Legend costLegend = asm.createLegend(new LegendMapping(asm.createAbstractElements(costs, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<Legend> legends = asm.getSurroundingLegends(new CellSpaceInformation(0,2,1), new CellSpaceInformation(0,3,4), 1);
		assertEquals("Surrounding legends", 2, legends.size());
		
		legends = asm.getSurroundingLegends(new CellSpaceInformation(0,3,1), new CellSpaceInformation(0,3,4), 1);
		assertEquals("Cost Legend (Size)", 1, legends.size());
		assertEquals("Cost Legend", costLegend, legends.get(0));
		
		legends = asm.getSurroundingLegends(new CellSpaceInformation(0,2,2), new CellSpaceInformation(0,3,4), 1);
		assertEquals("Year Legend (Size)", 1, legends.size());
		assertEquals("Year Legend", yearLegend, legends.get(0));
		
		legends = asm.getSurroundingLegends(new CellSpaceInformation(0,3,2), new CellSpaceInformation(0,3,4), 1);
		assertEquals("No Legend (Size)", 0, legends.size());
	}
	
	@Test
	public void testSerialization() {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		List<CellSpaceInformation> positionsCosts = new ArrayList<CellSpaceInformation>();
		positionsCosts.add(new CellSpaceInformation(0,2,0));
		positionsCosts.add(new CellSpaceInformation(0,3,0));
		positionsCosts.add(new CellSpaceInformation(0,4,0));
		asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsCosts, StructureCreateParameter.DataParameter.AllDiff), null, null));
		
		LegendProduct legendProduct = new LegendProduct(asm.getAllLegends());
		
		List<CellSpaceInformation> fbPositions = asm.filterEmpty(asm.createCellSpaceInformation(
				new CellSpaceInformation(0,2,1), new CellSpaceInformation(0,3,4)));
		
		Map<CellSpaceInformation, AbstractSsElement> elements = asm.createAbstractElements(fbPositions, StructureCreateParameter.DataParameter.AllDiff);
		Map<CellSpaceInformation, LegendProductEntry> domain = asm.createDomainInformation(fbPositions, asm.getAllLegends());
		
		asm.createFB(new FunctionalBlockMapping(legendProduct, elements, domain));
		
		sally.ModelDataMsg modelDataMsg = asm.getProtoBufRepresentation();
		
		ModelAdministrator asmReconstructed = new ModelAdministrator();
		asmReconstructed.createModel(modelDataMsg);
				
		assertEquals("Serialisation", asm, asmReconstructed);
	}
	
	@Test
	public void testSearchDependencies() {
		List<Legend> legends = new ArrayList<Legend>();
		
		List<CellSpaceInformation> positionsType = new ArrayList<CellSpaceInformation>();
		positionsType.add(new CellSpaceInformation(0,0,1,2,1));
		positionsType.add(new CellSpaceInformation(0,0,3,2,1));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsType, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<List<CellSpaceInformation>> dependencies = asm.searchDependencies(legends, new ArrayList<CellSpaceInformation>(), 0);
		assertEquals("Found paths", 4, dependencies.size());
		
	}
	
	@Test
	public void testCreateDependingLegendPositions() {
		List<Legend> legends = new ArrayList<Legend>();
		
		List<CellSpaceInformation> positionsType = new ArrayList<CellSpaceInformation>();
		positionsType.add(new CellSpaceInformation(0,0,1,2,1));
		positionsType.add(new CellSpaceInformation(0,0,3,2,1));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsType, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
	
		LegendProduct dependency = asm.createDependingLegendPositions(new RangeCoordinates(new CellSpaceInformation(0,0,1), new CellSpaceInformation(0,1,4)));
		assertEquals("Number of LegendProductEntries", 4, dependency.getEntries().size());
		assertEquals("Number of depending positions of cell (1/2)", 3, asm.getDependingLegendPositions(new CellSpaceInformation(0,0,1,2,1)).size());
		
	}
	
	
	private List<Legend> setupLegends() {
		List<Legend> legends = new ArrayList<Legend>();
		
		List<CellSpaceInformation> positionsType = new ArrayList<CellSpaceInformation>();
		positionsType.add(new CellSpaceInformation(0,0,1,2,1));
		positionsType.add(new CellSpaceInformation(0,0,3,2,1));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsType, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		positions.add(new CellSpaceInformation(0,1,1));
		positions.add(new CellSpaceInformation(0,1,2));
		positions.add(new CellSpaceInformation(0,1,3));
		positions.add(new CellSpaceInformation(0,1,4));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positions, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<CellSpaceInformation> positionsCosts = new ArrayList<CellSpaceInformation>();
		positionsCosts.add(new CellSpaceInformation(0,2,0));
		positionsCosts.add(new CellSpaceInformation(0,3,0));
		positionsCosts.add(new CellSpaceInformation(0,4,0));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positionsCosts, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		List<CellSpaceInformation> positionHeader = new ArrayList<CellSpaceInformation>();
		positionHeader.add(new CellSpaceInformation(0,0,0));
		legends.add( asm.createLegend(new LegendMapping(asm.createAbstractElements(positionHeader, StructureCreateParameter.DataParameter.AllDiff), null, null)) );
		
		return legends;
	}

}
