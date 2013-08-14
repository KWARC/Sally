package info.kwarc.sally.model.document.spreadsheet;

import info.kwarc.sally.model.ontology2.OntologyLinkedFB;
import info.kwarc.sally.model.ontology2.OntologyLinkedLegendSubType;
import info.kwarc.sally.model.ontology2.OntologyLinkedStructure;
import info.kwarc.sally.model.ontology2.OntologyMapping;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.CellPosition;
import sally.SpreadsheetOntologyPair;
import sally.WorksheetIDPair;

import com.hp.hpl.jena.rdf.model.Model;


public class ASMInterface {
	
	OntologyMapping ontoMapping;
	ModelAdministrator modelAdmin;
	Map<String, Integer> worksheetNames;
	final static int borderArea = 3;
	String documentURI;
	final Logger logger = LoggerFactory.getLogger(ASMInterface.class);
	
	public ASMInterface(String documentURI) {
		this.documentURI = documentURI;
		modelAdmin = new ModelAdministrator();
		ontoMapping = new OntologyMapping();
		worksheetNames = new HashMap<String, Integer>();
	}
	
	public Model getRDFModel() {
		return ontoMapping.getRDFModel();
	}
	
	public void addOntologyLink(Integer data, String ontologyURI) {
		AbstractStructure structure = modelAdmin.getStructureForId(data);
		OntologyLinkedStructure ontoStructure = null;
		
		if (structure instanceof Legend) {
			ontoStructure  = new OntologyLinkedLegendSubType(documentURI, ontologyURI, (Legend) structure);
		} else {
			ontoStructure  = new OntologyLinkedFB(documentURI, ontologyURI, (FunctionalBlock) structure);
		}
	
		ontoMapping.addMapping(ontoStructure, structure);
	}
	
	
	public List<Integer> getListOntologyStructures(String URI) {
		List<Integer> result = new ArrayList<Integer>();
		for (AbstractStructure struct : ontoMapping.getAllStructures()) {
			if (ontoMapping.getLinkingFor(struct).getMainURI().equals(URI))
				result.add(struct.getId());
		}		
		return result;
	}
	
	public String getOntologyForPosition(CellPosition pos) {
		AbstractStructure elem = modelAdmin.getAbstractStructureForPosition(new CellSpaceInformation(pos));
		if (elem == null)
			return null;
		OntologyLinkedStructure link = ontoMapping.getLinkingFor(elem);
		if (link == null)
			return null;
		return link.getMainURI();
	}
	
	public Integer getWorksheetIDByName(String name) {
		int id = -1;
		if (worksheetNames.containsKey(name))
			id = worksheetNames.get(name);
		else {
			int maxId = 0;
			for (Integer i : worksheetNames.values())
				maxId = java.lang.Math.max(maxId, i);
			id = maxId+1;
			worksheetNames.put(name, id);
		}
		
		return id;
	}
	
	public void setContent(sally.CellData cellInformation) {
		CellSpaceInformation pos = new CellSpaceInformation(cellInformation.getPosition());
		modelAdmin.setContent(pos, cellInformation.getValue(), cellInformation.getFormula());
	}
	
	public void setContent(sally.RangeData cellInformations) {
		for (sally.CellData data : cellInformations.getCellsList()) {
			setContent(data);
		}
	}
	
	public Integer createLegend(sally.LegendCreateData dataMsg ) {
		setContent(dataMsg.getItems());
		
		List<CellSpaceInformation> legendPositions = modelAdmin.filterEmpty(convertRangeDataToPos(dataMsg.getItems()));
		
		AbstractSsElement header = null;
		CellSpaceInformation headerPosition = null;
		
		sally.CellData headerData = dataMsg.getHeader();
		if (dataMsg.hasHeader()) {
			setContent(headerData);
			headerPosition = new CellSpaceInformation(headerData.getPosition());
			header = modelAdmin.createAbstractElement( headerPosition );
		}
		
		StructureCreateParameter.DataParameter param = StructureCreateParameter.DataParameter.AllDiff;
		if (dataMsg.hasParameter()) 
			param = StructureCreateParameter.DataParameter.values()[dataMsg.getParameter().ordinal()];
	
		return modelAdmin.createLegend(new LegendMapping(modelAdmin.createAbstractElements(legendPositions, param), headerPosition, header)).getId();
	}
		
	public Integer createFB(sally.FBCreateData dataMsg) {
		setContent(dataMsg.getRange());
		
		List<Legend> legends = modelAdmin.getLegendsForIds(dataMsg.getLegendsList());
		List<CellSpaceInformation> fbPositions = modelAdmin.filterEmpty(convertRangeDataToPos(dataMsg.getRange()));
		
		
		StructureCreateParameter parameter = convertCreateDataToFBCreateParameter(dataMsg);
		
		Map<CellSpaceInformation, AbstractSsElement> elements = modelAdmin.createAbstractElements(fbPositions, parameter.getDataParam());
		Map<CellSpaceInformation, LegendProductEntry> domain = modelAdmin.createDomainInformation(fbPositions, legends);
		
		LegendProduct legendProduct = new LegendProduct(legends);
		return modelAdmin.createFB(new FunctionalBlockMapping(legendProduct, elements, domain)).getId();
	}
	
	public List<Integer> getFunctionalBlockIDs(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation( range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return Util.convertFBsToIds( modelAdmin.getFBsForArea(startPos, endPos) );
	}
	
	public List<Integer> getAllFunctionalBlocks() {
		return Util.convertFBsToIds( modelAdmin.getAllFbs() );
	}

	public List<Integer> getLabelBlockIDs(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return Util.convertLegendsToIds( modelAdmin.getLegendsForArea(startPos, endPos) );
	}
	
	public sally.RangeSelection getBlockPosition(int blockId) {
		List<CellSpaceInformation> positions = modelAdmin.getPositionsForStructure(modelAdmin.getStructureForId(blockId));
		if (!positions.isEmpty()) {
			int worksheet = positions.get(0).getWorksheet();
			int startRow = positions.get(0).getRow();
			int startColumn = positions.get(0).getColumn();
			int endRow = positions.get(0).getRow();
			int endColumn = positions.get(0).getColumn();
			positions.remove(0);
			for (CellSpaceInformation pos : positions) {
				startRow = java.lang.Math.min(startRow, pos.getRow());
				startColumn = java.lang.Math.min(startColumn, pos.getColumn());
				endRow = java.lang.Math.max(endRow, pos.getRow());
				endColumn = java.lang.Math.max(endColumn, pos.getColumn());
				if ((worksheet < 0) && (pos.getWorksheet() >= 0))
					worksheet = pos.getWorksheet();
			}
			sally.RangeSelection.Builder rangeMsg = sally.RangeSelection.newBuilder();
			rangeMsg.setStartRow(startRow);
			rangeMsg.setStartCol(startColumn);
			rangeMsg.setEndRow(endRow);
			rangeMsg.setEndCol(endColumn);
			rangeMsg.setSheet(new Integer(worksheet).toString());
			return rangeMsg.build();
		} else 
			return null;
	}
	
	public List<Integer> getSurroundingLegends(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return Util.convertLegendsToIds( modelAdmin.getSurroundingLegends(startPos, endPos, borderArea) );
	}
	
	/**
	 * Gives a list of cells that are associated with the cell given as parameter. Example:
	 *  
	 * @param cell
	 * @return
	 */
	public sally.CellPositions getDependentCells(sally.CellSpaceInformation position) {
		List<CellSpaceInformation> positions = modelAdmin.getDependingLegendPositions(new CellSpaceInformation(position));
		sally.CellPositions.Builder positionsMsg = sally.CellPositions.newBuilder();
		for (CellSpaceInformation pos : positions)
			positionsMsg.addCellPositions(pos.getProtoBufRepresentation());
		return positionsMsg.build();
	}
	
	public List<Integer> getLegendsinArea(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return Util.convertLegendsToIds( modelAdmin.getLegendsForArea(startPos, endPos) );
	}
	
	public sally.SpreadsheetModel serialize() {
		sally.SpreadsheetModel.Builder model = sally.SpreadsheetModel.newBuilder();
		model.setAsm(modelAdmin.getProtoBufRepresentation());
		for (AbstractStructure struct : ontoMapping.getAllStructures()) {
			model.addOntomapping(SpreadsheetOntologyPair.newBuilder()
					.setAsmid(struct.getId())
					.setUri(ontoMapping.getLinkingFor(struct).getMainURI())).build();
			// sally.RangeSelection range = getBlockPosition(struct.getId());  // ?			
		}
		
		for (String worksheet : worksheetNames.keySet()) {
			model.addSheetMapping(sally.WorksheetIDPair.newBuilder()
					.setWorksheet(worksheet)
					.setId(worksheetNames.get(worksheet)).build());
		}
		
		return model.build();
	}
	
	public void reconstruct(sally.SpreadsheetModel modelData) {
		modelAdmin.createModel(modelData.getAsm());
		for (SpreadsheetOntologyPair pair : modelData.getOntomappingList()) {
			addOntologyLink(pair.getAsmid(), pair.getUri());
		}
		for (WorksheetIDPair pair : modelData.getSheetMappingList()) {
			worksheetNames.put(pair.getWorksheet(), pair.getId());
		}
		
	}
	
	public sally.CellPositions getRelevantLegendPositions(sally.CellSpaceInformation position) {
		List<CellSpaceInformation> positions = modelAdmin.getLegendItems(new CellSpaceInformation(position));
		sally.CellPositions.Builder positionsMsg = sally.CellPositions.newBuilder();
		for (CellSpaceInformation p : positions) {
			positionsMsg.addCellPositions(p.getProtoBufRepresentation());
		}
		return positionsMsg.build();
	}
	

	private List<CellSpaceInformation> convertRangeDataToPos(sally.RangeData data) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		for (sally.CellData cellData : data.getCellsList())
			positions.add(new CellSpaceInformation(cellData.getPosition()));
		return positions;
	}
	
	private StructureCreateParameter convertCreateDataToFBCreateParameter(sally.FBCreateData msg) {
		StructureCreateParameter p = new StructureCreateParameter();
		if (msg.hasParameter())
			p.setDataParam( StructureCreateParameter.DataParameter.values()[msg.getParameter().ordinal()] );
		
		
		if (msg.getConnectToAllCount() > 0) {
			p.setConnectToAll(msg.getConnectToAllList());
		}
		
		return p;
	}

}
