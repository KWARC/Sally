package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sissi.model.ontology2.OntologyLinkedFB;
import info.kwarc.sissi.model.ontology2.OntologyLinkedLegendSubType;
import info.kwarc.sissi.model.ontology2.OntologyLinkedStructure;
import info.kwarc.sissi.model.ontology2.OntologyMapping;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.CellPosition;
import sally.IdData;
import sally.SpreadsheetOntologyPair;

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
	
	public void addOntologyLink(sally.IdData data, String ontologyURI) {
		AbstractStructure structure = modelAdmin.getStructureForId(data.getId());
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
		return ontoMapping.getLinkingFor(elem).getMainURI();
	}
	
	public sally.IdData getWorksheetIDByName(sally.StringData name) {
		int id = -1;
		if (worksheetNames.containsKey(name.getName()))
			id = worksheetNames.get(name.getName());
		else {
			int maxId = 0;
			for (Integer i : worksheetNames.values())
				maxId = java.lang.Math.max(maxId, i);
			id = maxId+1;
			worksheetNames.put(name.getName(), id);
		}
		
		sally.IdData.Builder idMsg = sally.IdData.newBuilder();
		idMsg.setId(id);
		return idMsg.build();
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
	
	public sally.IdData createLegend(sally.LegendCreateData dataMsg ) {
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
	
		return convertIdToMsg(modelAdmin.createLegend(new LegendMapping(modelAdmin.createAbstractElements(legendPositions, param), headerPosition, header)).getId() );
	}
		
	public sally.IdData createFB(sally.FBCreateData dataMsg) {
		setContent(dataMsg.getRange());
		
		List<Legend> legends = modelAdmin.getLegendsForIds(convertIdMsgToList(dataMsg.getLegends()));
		List<CellSpaceInformation> fbPositions = modelAdmin.filterEmpty(convertRangeDataToPos(dataMsg.getRange()));
		
		
		StructureCreateParameter parameter = convertCreateDataToFBCreateParameter(dataMsg);
		
		Map<CellSpaceInformation, AbstractSsElement> elements = modelAdmin.createAbstractElements(fbPositions, parameter.getDataParam());
		Map<CellSpaceInformation, LegendProductEntry> domain = modelAdmin.createDomainInformation(fbPositions, legends);
		
		LegendProduct legendProduct = new LegendProduct(legends);
		return convertIdToMsg(modelAdmin.createFB(new FunctionalBlockMapping(legendProduct, elements, domain)).getId() );

	}
	
	public sally.IdList getFunctionalBlockIDs(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation( range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return convertIdListToMsg( Util.convertFBsToIds( modelAdmin.getFBsForArea(startPos, endPos) ) );
	}
	
	public sally.IdList getAllFunctionalBlocks() {
		return convertIdListToMsg( Util.convertFBsToIds( modelAdmin.getAllFbs() ) );
	}

	public sally.IdList getLabelBlockIDs(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return convertIdListToMsg( Util.convertLegendsToIds( modelAdmin.getLegendsForArea(startPos, endPos) ));
	}
	
	public sally.RangeSelection getBlockPosition(sally.IdData idMsg) {
		Integer blockId = idMsg.getId();
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
	
	public sally.IdList getSurroundingLegends(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return convertIdListToMsg( Util.convertLegendsToIds( modelAdmin.getSurroundingLegends(startPos, endPos, borderArea) ) );
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
	
	public sally.IdList getLegendsinArea(sally.RangeSelection range) {
		CellSpaceInformation startPos = new CellSpaceInformation(range.getStartRow(), range.getStartCol());
		CellSpaceInformation endPos = new CellSpaceInformation(range.getEndRow(), range.getEndCol());
		return convertIdListToMsg( Util.convertLegendsToIds( modelAdmin.getLegendsForArea(startPos, endPos) ) );
	}
	
	public sally.SpreadsheetModel serialize() {
		sally.SpreadsheetModel.Builder model = sally.SpreadsheetModel.newBuilder();
		model.setAsm(modelAdmin.getProtoBufRepresentation());
		for (AbstractStructure struct : ontoMapping.getAllStructures()) {
			model.addOntomapping(SpreadsheetOntologyPair.newBuilder()
					.setAsmid(IdData.newBuilder().setId(struct.getId()).build())
					.setUri(ontoMapping.getLinkingFor(struct).getMainURI())).build();
		}
		return model.build();
	}
	
	public void reconstruct(sally.SpreadsheetModel modelData) {
		modelAdmin.createModel(modelData.getAsm());
		for (SpreadsheetOntologyPair pair : modelData.getOntomappingList()) {
			
			addOntologyLink(pair.getAsmid(), pair.getUri());
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
	
	private sally.IdList convertIdListToMsg(List<Integer> ids) {
		sally.IdList.Builder idListMsg = sally.IdList.newBuilder();
		for (Integer id : ids) {
			sally.IdData.Builder idMsg = sally.IdData.newBuilder();
			idMsg.setId(id);
			idListMsg.addIds(idMsg);
		}
		return idListMsg.build();
	}
	
	private List<Integer> convertIdMsgToList(sally.IdList idListMsg) {
		List<Integer> ids = new ArrayList<Integer>();
		
		for (sally.IdData id : idListMsg.getIdsList())
			ids.add(id.getId());
		
		return ids;
	}
	
	private sally.IdData convertIdToMsg(int id) {
		sally.IdData.Builder idMsg = sally.IdData.newBuilder();
		idMsg.setId(id);
		return idMsg.build();
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
		
		
		if (msg.hasConnectToAll()) {
			p.setConnectToAll( convertIdMsgToList(msg.getConnectToAll()) );
		}
		
		return p;
	}

}
