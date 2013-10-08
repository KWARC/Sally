package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ModelAdministrator {
	

	
	AbstractSsModel asm;
	FormalSpreadsheet fsm;
	MappingManager mappings;
	int absStrucId;
	
	final Logger logger = LoggerFactory.getLogger(ModelAdministrator.class);
	
	public ModelAdministrator() {
		initModel();
	}
	
	public void initModel() {
		asm = new AbstractSsModel();
		fsm = new FormalSpreadsheet();
		mappings = new MappingManager();
		absStrucId = 0;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + absStrucId;
		result = prime * result + ((asm == null) ? 0 : asm.hashCode());
		result = prime * result
				+ ((mappings == null) ? 0 : mappings.hashCode());
		return result;
	}

	/**
	 * Test if the abstract spreadsheet model, mapping and maxId are equal. The formal spreadsheet is left out, because it is just temporarily set.
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ModelAdministrator other = (ModelAdministrator) obj;
		if (absStrucId != other.absStrucId)
			return false;
		if (asm == null) {
			if (other.asm != null)
				return false;
		} else if (!asm.equals(other.asm))
			return false;
		if (mappings == null) {
			if (other.mappings != null)
				return false;
		} else if (!mappings.equals(other.mappings))
			return false;
		return true;
	}

	public void setContent(CellSpaceInformation position, String value, String formula) {
		fsm.setContent(position, value, Util.identifyValueType(value));
	}
	
	public void createModel(sally.ModelDataMsgOld modelData) {
		initModel();
		AbstractDataModel adm = asm.getDataModel();
		
		// Create abstract elements
		sally.AbstractDataModelMsg admMsg = modelData.getAsm().getElements();
		for (sally.AbstractElementMsg e : admMsg.getElementsList() ) {
			String value = e.getValue();
			adm.createElement(e.getId(), value, Util.identifyValueType(value));
		}
		
		// Set parameters for the abstract elements
		for (sally.AbstractElementMsg e : admMsg.getElementsList() ) {
			AbstractSsElement element = adm.getElementById(e.getId());
			List<AbstractSsElement> parameters = new ArrayList<AbstractSsElement>();
			for (int paramId : e.getParametersList())
				parameters.add(adm.getElementById(paramId));
			element.setParameters(parameters);
		}
		
		// Create labels
		for (sally.LegendMsg legendMsg : modelData.getAsm().getLegendsList() ) {
			int legendId = legendMsg.getId();
			AbstractSsElement header = null;
			if (legendMsg.hasHeader())
				header = adm.getElementById(legendMsg.getHeader());
			List<AbstractSsElement> legendItems = new ArrayList<AbstractSsElement>();
			for (Integer itemId : legendMsg.getItemsList())
				legendItems.add(adm.getElementById(itemId));
			asm.addLegend(new Legend(legendId, header, legendItems));
			if (absStrucId == legendId)
				absStrucId++;
			else
				absStrucId = java.lang.Math.max(absStrucId, legendId+1);
		}
			
		// Create functional blocks
		for (sally.FunctionalBlockMsg fbMsg : modelData.getAsm().getFunctionalBlocksList()) {
			int fbId = fbMsg.getId();
			List<Legend> domainLegends = new ArrayList<Legend>();
			for (Integer legendId : fbMsg.getDomain().getLegendsList())
				domainLegends.add(asm.getLegendById(legendId));
			LegendProduct domain = new LegendProduct(domainLegends);
			FunctionalBlock fb = new FunctionalBlock(fbId, domain);
			for (sally.FBEntryMsg fbEntryMsg : fbMsg.getEntryList()) {
				List<Legend> entryLegends = new ArrayList<Legend>();
				for (Integer elId : fbEntryMsg.getDomainElem().getLegendsList())
					entryLegends.add(asm.getLegendById(elId));
				List<AbstractSsElement> domainElement = new ArrayList<AbstractSsElement>();
				for (Integer absElId : fbEntryMsg.getDomainElem().getElementsList())
					domainElement.add(asm.getDataModel().getElementById(absElId));
				LegendProductEntry domainEntry = new LegendProductEntry(entryLegends, domainElement);
				fb.addEntry(domainEntry, asm.getDataModel().getElementById(fbEntryMsg.getAbsElemId()));
			}
			asm.addFunctionalBlock(fb);
			if (absStrucId == fbId)
				absStrucId++;
			else
				absStrucId = java.lang.Math.max(absStrucId, fbId+1);
		}
		
		// Create Legend Mappings
		for (sally.LegendMappingMsg legendMapping : modelData.getMapping().getLegendMappingsList()) {
			AbstractStructure mappingStruc = asm.getLegendById( legendMapping.getLegendId() );
			CellSpaceInformation headerPosition = null;
			if (legendMapping.hasHeaderPosition())
				headerPosition = new CellSpaceInformation(legendMapping.getHeaderPosition());
			AbstractSsElement header = null;
			if (legendMapping.hasHeaderElementId())
				header = asm.getDataModel().getElementById( legendMapping.getHeaderElementId() );
			
			Map <CellSpaceInformation, AbstractSsElement> mapping = new HashMap<CellSpaceInformation, AbstractSsElement>();
			for (sally.ElementMappingMsg elementMapping : legendMapping.getElementPositionsList()) {
				CellSpaceInformation pos = new CellSpaceInformation(elementMapping.getPosition());
				AbstractSsElement el = asm.getDataModel().getElementById(elementMapping.getAbsElemId());
				mapping.put(pos, el);
			}
			mappings.addMap(new LegendMapping(mapping, headerPosition, header), mappingStruc);
		}
		
		// Create FunctionalBlock Mappings
		for (sally.FunctionalBlockMappingMsg fbMapping : modelData.getMapping().getFbMappingsList()) {
			AbstractStructure mappingStruc = asm.getFBById( fbMapping.getFbId() );
			Map<CellSpaceInformation, AbstractSsElement> mapping = new HashMap<CellSpaceInformation, AbstractSsElement>();
			for (sally.ElementMappingMsg elementMapping : fbMapping.getElementMappingList()) {
				CellSpaceInformation pos = new CellSpaceInformation(elementMapping.getPosition());
				AbstractSsElement el = asm.getDataModel().getElementById(elementMapping.getAbsElemId());
				mapping.put(pos, el);
			}
			Map<CellSpaceInformation, LegendProductEntry> domainMapping = new HashMap<CellSpaceInformation, LegendProductEntry>();
			for (sally.DomainMappingMsg elementDomain : fbMapping.getDomainMappingList()) {
				CellSpaceInformation pos = new CellSpaceInformation(elementDomain.getPosition());
				List<Legend> entryLegends = new ArrayList<Legend>();
				for (Integer elId : elementDomain.getDomainElement().getLegendsList())
					entryLegends.add(asm.getLegendById(elId));
				List<AbstractSsElement> domainElement = new ArrayList<AbstractSsElement>();
				for (Integer absElId : elementDomain.getDomainElement().getElementsList())
					domainElement.add(asm.getDataModel().getElementById(absElId));
				LegendProductEntry domainEntry = new LegendProductEntry(entryLegends, domainElement);
				domainMapping.put(pos, domainEntry);
			}
			List<Legend> domainLegends = new ArrayList<Legend>();
			for (Integer legendId : fbMapping.getDomain().getLegendsList())
				domainLegends.add(asm.getLegendById(legendId));
			LegendProduct domain = new LegendProduct(domainLegends);
			mappings.addMap(new FunctionalBlockMapping(domain, mapping, domainMapping), mappingStruc);
		}
	}
	
	public Legend createLegend(LegendMapping mapping) {
		Legend l = new Legend(absStrucId, mapping.getLegendHeader(), mapping.getLegendItems());
		absStrucId++;
		asm.addLegend(l);
		mappings.addMap(mapping, l);
		return l;
	}
	
	public FunctionalBlock createFB(FunctionalBlockMapping mapping) {
		FunctionalBlock fb = new FunctionalBlock(absStrucId, mapping.getDomain());
		absStrucId++;
		for (CellSpaceInformation pos : mapping.getAllPositions() )
			fb.addEntry(mapping.getDomainEntryFor(pos), mapping.getElementFor(pos));
		asm.addFunctionalBlock(fb);
		mappings.addMap(mapping, fb);
		return fb;
	}
	
	public AbstractSsElement createAbstractElement(CellSpaceInformation position) {
		FormalSsElement element = fsm.get(position);
		if (element != null) {
			List<AbstractSsElement> parameters = new ArrayList<AbstractSsElement>();
			for (CellSpaceInformation paraPos : element.getParameters()) {
				AbstractSsElement parameter = mappings.getElementFor(paraPos);
				if (parameter != null)
					parameters.add(parameter);
				else
					throw new java.lang.IllegalArgumentException("Could not find element for parameter at position: " + paraPos.toString());
			}
			return asm.getDataModel().createElement(element.getValue(), element.getValueType(), parameters); 
		} else
			return null;
	}
	
	public Map<CellSpaceInformation, AbstractSsElement> createAbstractElements(List<CellSpaceInformation> positions, StructureCreateParameter.DataParameter param) {
		Map<CellSpaceInformation, AbstractSsElement> absElements = new LinkedHashMap<CellSpaceInformation,AbstractSsElement>();
		Map<String, AbstractSsElement> valueToElement = new HashMap<String, AbstractSsElement>();
		for (CellSpaceInformation position : positions) {
			String value = fsm.get(position).getValue();
			if (param.equals(StructureCreateParameter.DataParameter.AllDiff))
				absElements.put(position, createAbstractElement(position));
			else if (param.equals(StructureCreateParameter.DataParameter.SameContentSameElement) || param.equals(StructureCreateParameter.DataParameter.SameStringSameElement) ) {
				if (valueToElement.containsKey(value))
					absElements.put(position, valueToElement.get(value));
				else {
					AbstractSsElement el = createAbstractElement(position);
					absElements.put(position, el);
					if (param.equals(StructureCreateParameter.DataParameter.SameContentSameElement) || Util.isString(value, false) )
						valueToElement.put(value, el);
				}
			}
		}
		return absElements;
	}
	
	
	public Map<CellSpaceInformation, LegendProductEntry> createDomainInformation(List<CellSpaceInformation> positions, List<Legend> legends) {
		 return createDomainInformation(positions, legends, null);
	}
	
	public Map<CellSpaceInformation, LegendProductEntry> createDomainInformation(List<CellSpaceInformation> positions, List<Legend> legends, StructureCreateParameter parameter) {
		 Map<CellSpaceInformation, LegendProductEntry> domain = new  HashMap<CellSpaceInformation, LegendProductEntry>();
		 
		 List<Legend> automaticAssociated  = new ArrayList<Legend>();
		 List<Legend> connectToAllElements = new ArrayList<Legend>();
		 
		 if (parameter != null) {
			 for (Legend l : legends) {
				 if (parameter.getConnectToAll().contains(new Integer(l.getId())))
					 connectToAllElements.add(l);
				 else
					 automaticAssociated.add(l);
			 }
		 } else 
			 automaticAssociated = legends;
		 
		 for (CellSpaceInformation position : positions) {
			 	 
			 Map<Legend,List<CellSpaceInformation>> assocPositions = getAssociatedCells(position, automaticAssociated);
			 List<AbstractSsElement> legendTuple = new ArrayList<AbstractSsElement>();
			 
			 for (Legend l : automaticAssociated) {
				 List<CellSpaceInformation> assocLegendPositions = assocPositions.get(l);
				 if (assocLegendPositions.size() == 0) {
					 logger.info(String.format("Position %s does not have a corresponding label entry.", position));
				 } else if (assocLegendPositions.size() > 1)
					 logger.info(String.format("Positions %s depends on multiple elements of one label.", position));
				 else
					 legendTuple.add(mappings.getElementFor(assocLegendPositions.get(0)));
			 }
			 
			 for (Legend l : connectToAllElements) {
				 for (AbstractSsElement e : l.getItems()) {
					 legendTuple.add(e);
				 }
			 }
			 
			 domain.put(position, new LegendProductEntry(legends, legendTuple));
		 }
		 
		 return domain;
	}
	
	public List<CellSpaceInformation> createCellSpaceInformation(CellSpaceInformation start, CellSpaceInformation end) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		
		if (start.getWorksheet() != end.getWorksheet()) 
			throw new java.lang.IllegalArgumentException("Start and endposition are on different worksheets.");
		
		for (int row = start.getRow(); row <= end.getRow(); row++) {
			for (int column = start.getColumn(); column <= end.getColumn(); column++) {
				positions.add(new CellSpaceInformation(start.getWorksheet(), row, column));
			}
		}
		
		return positions;
	}
	
	public LegendProduct createDependingLegendPositions(RangeCoordinates range) {
		List<Legend> legends = getLegendsForArea(range.getStartPosition(), range.getEndPosition());
		List<List<CellSpaceInformation>> dependencies = searchDependencies(legends, new ArrayList<CellSpaceInformation>(), 0);
		LegendProduct dependency = new LegendProduct(legends);
		
		for (List<CellSpaceInformation> path : dependencies) {
			List<AbstractSsElement> elements = new ArrayList<AbstractSsElement>();
			for (CellSpaceInformation pos : path)
				elements.add(mappings.getElementFor(pos));
			dependency.addEntry(elements);
		}
		asm.addLegendDependency(dependency);
		return dependency;
		
	}
	
	// Getters by id
	
	public List<Legend> getAllLegends() {
		return asm.getLegends();
	}
	
	public Legend getLegendForId(int id) {
		return asm.getLegendById(id);
	}
	
	public List<Legend> getLegendsForIds(List<Integer> ids) {
		return Util.convertIdsToLegends(ids, asm);
	}
	
	public List<FunctionalBlock> getAllFbs() {
		return asm.getFunctionalBlocks();
	}
	
	public FunctionalBlock getFBForId(int id) {
		return asm.getFBById(id);
	}
	
	public List<FunctionalBlock> getFBsForIds(List<Integer> ids) {
		return Util.convertIdsToFBs(ids, asm);
	}
	
	public List<AbstractStructure> getAllStructures() {
		List<AbstractStructure> structures = new ArrayList<AbstractStructure>();
		
		for (Legend l : getAllLegends())
			structures.add(l);
		
		for (FunctionalBlock fb : getAllFbs())
			structures.add(fb);
		
		return structures;
	}
	
	public AbstractStructure getStructureForId(int id) {
		Legend l = getLegendForId(id);
		if (l != null)
			return l;
		else
			return getFBForId(id);
	}
	
	public List<AbstractStructure> getStructuresForIds(List<Integer> ids) {
		List<AbstractStructure> structures = new ArrayList<AbstractStructure>();
		
		for (Legend l : getLegendsForIds(ids))
			structures.add(l);
		
		for (FunctionalBlock fb : getFBsForIds(ids))
			structures.add(fb);
		
		return structures;
	}
	
	// Getters for positions
	
	public AbstractSsElement getElementForPosition(CellSpaceInformation pos) {
		return mappings.getElementFor(pos);
	}

	public AbstractStructure getAbstractStructureForPosition(CellSpaceInformation pos) {
		return  mappings.getAbstractStructureFor(pos);
	}

	public List<Legend> getLegendsForArea(CellSpaceInformation start, CellSpaceInformation end) {
		List<Legend> legends = new ArrayList<Legend>();
		
		List<CellSpaceInformation> positions = createCellSpaceInformation(start, end);
		for (CellSpaceInformation pos : positions) {
			AbstractStructure s = mappings.getAbstractStructureFor(pos);
			if (s instanceof Legend) {
				Legend legend = (Legend) s;
				if (!legends.contains(legend))
					legends.add(legend);
			}
		}
		return legends;
	}
	
	public Legend getLegendforPosition(CellSpaceInformation pos) {
		AbstractStructure s = mappings.getAbstractStructureFor(pos);
		if ((s != null) && (s instanceof Legend))
			return (Legend) s;
		else
			return null;
	}
	
	public List<FunctionalBlock> getFBsForArea(CellSpaceInformation start, CellSpaceInformation end) {
		List<FunctionalBlock> fbs = new ArrayList<FunctionalBlock>();
		
		List<CellSpaceInformation> positions = createCellSpaceInformation(start, end);
		for (CellSpaceInformation pos : positions) {
			AbstractStructure s = mappings.getAbstractStructureFor(pos);
			if (s instanceof FunctionalBlock) {
				FunctionalBlock fb = (FunctionalBlock) s;
				if (!fbs.contains(fb))
					fbs.add(fb);
			}
		}
		return fbs;
	}
	
	public FunctionalBlock getFBforPosition(CellSpaceInformation pos) {
		AbstractStructure s = mappings.getAbstractStructureFor(pos);
		if ((s != null) && (s instanceof FunctionalBlock))
			return (FunctionalBlock) s;
		else
			return null;
	}
	
	public MappingManager getMappingManager() {
		return this.mappings;
	}
	
	// Other Getters
	
	public Map<Legend,List<CellSpaceInformation>> getAssociatedCells(CellSpaceInformation position, List<Legend> legends) {
		Map<Legend,List<CellSpaceInformation>> assocPositions = new LinkedHashMap<Legend, List<CellSpaceInformation>>();
		
		for (Legend l : legends) {
			assocPositions.put(l, new ArrayList<CellSpaceInformation>());
			
			Mapping map = mappings.getMappingFor(l);
			if (map != null) {
				for (CellSpaceInformation itemPos : map.getAllPositions()) {
					if ( (itemPos.isAssociated(position) ) )
						assocPositions.get(l).add(itemPos);
				}	
			}
		}
		
		return assocPositions;
	}
	
	public List<Legend> getSurroundingLegends(CellSpaceInformation start, CellSpaceInformation end, int border) {
		List<Legend> legends = new ArrayList<Legend>();
		
		if (start.getWorksheet() != end.getWorksheet())
			throw new java.lang.IllegalArgumentException("Start and endposition are on different worksheets.");
		int worksheet = start.getWorksheet();
		
		for (int row = Math.max(start.getRow()-border, 0); row <= Math.min(end.getRow()+border, fsm.getMaxRow(worksheet)); row++) {
			for (int column = Math.max(start.getColumn()-border, 0); column <= Math.min(end.getColumn()+border, fsm.getMaxColumn(worksheet)); column++) {
				if (!( (start.getRow() <= row) && (row <= end.getRow()) && (start.getColumn() <= column) && (column <= end.getColumn()) ) ) {
					AbstractStructure s = mappings.getAbstractStructureFor(new CellSpaceInformation(worksheet, row, column));
					if (s instanceof Legend) {
						Legend legend = (Legend) s;
						if (!legends.contains(legend))
							legends.add(legend);
					}
				}
			}
		}
		return legends;
	}
	
	public List<CellSpaceInformation> getPositionsForStructure(AbstractStructure s) {
		return mappings.getMappingFor(s).getAllPositions();
	}
	
	public sally.ModelDataMsgOld getProtoBufRepresentation() {
		sally.ModelDataMsgOld.Builder msgBuilder = sally.ModelDataMsgOld.newBuilder();
		
		msgBuilder.setAsm(asm.getProtoBufRepresentation());
		msgBuilder.setMapping(mappings.getProtoBufRepresentation());

		return msgBuilder.build();
	}

	public  List<CellSpaceInformation> filterEmpty(List<CellSpaceInformation> positions) {
		 List<CellSpaceInformation> nonEmpty = new ArrayList<CellSpaceInformation>();
		 
		 for (CellSpaceInformation pos : positions)
			 if (!fsm.get(pos).getValue().isEmpty())
				 nonEmpty.add(pos);
		 
		 return nonEmpty;
	}
	
	
	public List<CellSpaceInformation> getLegendItems(CellSpaceInformation pos) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		AbstractStructure struc = mappings.getAbstractStructureFor(pos);
		if (struc instanceof FunctionalBlock) {
			FunctionalBlock fb = (FunctionalBlock) struc;
			AbstractSsElement el = mappings.getElementFor(pos);
			List<LegendProductEntry> entries = fb.getLegendElementsFor(el);
			for (LegendProductEntry e : entries) {
				positions.addAll(getAssociated(e, fb.getDomainLegends(), pos));
			}
		}
		return positions;
	}
	
	public List<CellSpaceInformation> getAssociated(LegendProductEntry entry, LegendProduct domain, CellSpaceInformation pos) {
		List<CellSpaceInformation> assocPositions = new ArrayList<CellSpaceInformation>();
		for (AbstractSsElement item : entry.getLegendTuple()) {
			// Find positions which are part of the domain
			List<CellSpaceInformation> relevantPositions = new ArrayList<CellSpaceInformation>();
			for (CellSpaceInformation itemPos : mappings.getPositionsFor(item)) {
				if ((mappings.getAbstractStructureFor(itemPos) instanceof Legend) && domain.containsLegend((Legend) mappings.getAbstractStructureFor(itemPos)) ) {
					//relevantPositions.add(itemPos);
					assocPositions.add(itemPos);
				}
			}

			// Find associated position 
			/* Does not work for associated elements with no spatial relation.
			Boolean isAssocItem = false;
			for (CellSpaceInformation itemPos : relevantPositions) {
				if ( itemPos.isAssociated(pos) ) {
					isAssocItem = true;
					if (!assocPositions.contains(itemPos))
						assocPositions.add(itemPos);
				}
			}
			if (!isAssocItem) {
				return new ArrayList<CellSpaceInformation>();
			}*/
		}
		return assocPositions;
	}
	

	
	public List<CellSpaceInformation> getDependingLegendPositions(CellSpaceInformation pos) {
		AbstractSsElement element = mappings.getElementFor(pos);
		Legend legend = (Legend)mappings.getAbstractStructureFor(pos);
		List<AbstractSsElement> dependingElements = asm.getDependeningLegendItems(element, legend);
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		for (AbstractSsElement e : dependingElements) {
			List<CellSpaceInformation> elementPositions = mappings.getPositionsFor(e);
			for (CellSpaceInformation elementPosition : elementPositions) {
				if (elementPosition.isAssociated(pos) && !positions.contains(elementPosition)) 
					positions.add(elementPosition);
			}
		}
		return positions;
	}
	
	public List<List<CellSpaceInformation>> searchDependencies(List<Legend> legends, List<CellSpaceInformation> path, int depth) {
		List<List<CellSpaceInformation>> dependingPositions = new ArrayList<List<CellSpaceInformation>>();
		Legend starting = legends.get(depth);
		for (int index = 0; index < starting.getItemSize(); index++) {
			AbstractSsElement elem = starting.getItems().get(index);
			List<CellSpaceInformation> positions = mappings.getMappingFor(starting).getPositionFor(elem);
			for (CellSpaceInformation pos : positions) {
				if (pos.isAssociated(path) && (depth < (legends.size()-1)) ) {
					List<CellSpaceInformation> newPath = new ArrayList<CellSpaceInformation>(path);
					newPath.add(pos);
					dependingPositions.addAll(searchDependencies(legends, newPath, depth+1 ));
				} else if (pos.isAssociated(path) && (depth == (legends.size()-1)) ) {
					List<CellSpaceInformation> newPath = new ArrayList<CellSpaceInformation>(path);
					newPath.add(pos);
					dependingPositions.add(newPath);
				}
			}
		}
		return dependingPositions;
	}
	

	
	
	
}
