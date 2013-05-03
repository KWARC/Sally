package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class MappingManager {
	Map<CellSpaceInformation, Mapping> posToMap;
	Map<AbstractSsElement, List<Mapping>> elemToMap;
	Map<AbstractStructure, Mapping> strucToMap;
	Map<CellSpaceInformation, AbstractStructure> posToStruc;
	
	public MappingManager() {
		posToMap = new HashMap<CellSpaceInformation, Mapping>();
		elemToMap = new HashMap<AbstractSsElement, List<Mapping>>();
		strucToMap = new HashMap<AbstractStructure, Mapping>();
		posToStruc = new HashMap<CellSpaceInformation, AbstractStructure>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((strucToMap == null) ? 0 : strucToMap.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		MappingManager other = (MappingManager) obj;
		if (strucToMap == null) {
			if (other.strucToMap != null)
				return false;
		} else if (!strucToMap.equals(other.strucToMap))
			return false;
		return true;
	}

	public void addMap(Mapping map, AbstractStructure absStruc) {
		for (CellSpaceInformation pos : map.getAllPositions()) {
			if (posToMap.containsKey(pos))
				throw new java.lang.IllegalArgumentException("Mapping for position " + pos.toString() + " is already available.");
			posToMap.put(pos, map);
			posToStruc.put(pos, absStruc);
		}
		for (AbstractSsElement elem : map.getAllElements()) {
			if (elemToMap.containsKey(elem))
				elemToMap.get(elem).add(map);
			else {
				List<Mapping> mappingList = new ArrayList<Mapping>();
				mappingList.add(map);
				elemToMap.put(elem, mappingList);
			}
		}
		strucToMap.put(absStruc, map);
	}
	
	public AbstractSsElement getElementFor(CellSpaceInformation pos) {
		return posToMap.get(pos).getElementFor(pos);
	}
	
	public List<CellSpaceInformation> getPositionsFor(AbstractSsElement element) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		
		if (elemToMap.containsKey(element)) {
			for (Mapping map : elemToMap.get(element))
				positions.addAll(map.getPositionFor(element));
		}
		
		return positions;
	}
	
	public Mapping getMappingFor(AbstractStructure struc) {
		return strucToMap.get(struc);
	}
	
	public AbstractStructure getAbstractStructureFor(CellSpaceInformation pos) {
		return posToStruc.get(pos);
	}
	
	public sally.MappingMsg getProtoBufRepresentation() {
		sally.MappingMsg.Builder msgBuilder = sally.MappingMsg.newBuilder();

		for (Entry<AbstractStructure, Mapping> mapping : strucToMap.entrySet()) {
			int strucId = mapping.getKey().getId();
			if ((mapping.getKey() instanceof Legend) && (mapping.getValue() instanceof LegendMapping) ) {
				LegendMapping lm = (LegendMapping) mapping.getValue();
				msgBuilder.addLegendMappings(lm.getProtoBufRepresentation(strucId));
			} else if ((mapping.getKey() instanceof FunctionalBlock) && (mapping.getValue() instanceof FunctionalBlockMapping)) {
				FunctionalBlockMapping fbm = (FunctionalBlockMapping) mapping.getValue();
				msgBuilder.addFbMappings(fbm.getProtoBufRepresentation(strucId));
			} else
				System.out.println("Inconsistent abstract structure - mapping pair can not be serialized.");
		}
		
		return msgBuilder.build();
	}
}
