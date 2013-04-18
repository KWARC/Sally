package info.kwarc.sissi.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class LegendMapping extends Mapping {
	Map<CellSpaceInformation, AbstractSsElement> itemMapping;
	CellSpaceInformation headerPosition;
	AbstractSsElement legendHeader;
	
	public LegendMapping(
			Map<CellSpaceInformation, AbstractSsElement> itemMapping,
			CellSpaceInformation headerPosition, AbstractSsElement legendHeader) {
		super();
		if (itemMapping != null)
			this.itemMapping = itemMapping;
		else
			this.itemMapping = new HashMap<CellSpaceInformation, AbstractSsElement>();
		this.headerPosition = headerPosition;
		this.legendHeader = legendHeader;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((headerPosition == null) ? 0 : headerPosition.hashCode());
		result = prime * result
				+ ((itemMapping == null) ? 0 : itemMapping.hashCode());
		result = prime * result
				+ ((legendHeader == null) ? 0 : legendHeader.hashCode());
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
		LegendMapping other = (LegendMapping) obj;
		if (headerPosition == null) {
			if (other.headerPosition != null)
				return false;
		} else if (!headerPosition.equals(other.headerPosition))
			return false;
		if (itemMapping == null) {
			if (other.itemMapping != null)
				return false;
		} else if (!itemMapping.equals(other.itemMapping))
			return false;
		if (legendHeader == null) {
			if (other.legendHeader != null)
				return false;
		} else if (!legendHeader.equals(other.legendHeader))
			return false;
		return true;
	}

	public void addItemMapping(CellSpaceInformation position, AbstractSsElement element) {
		if (itemMapping.containsKey(position) && !itemMapping.get(position).equals(element)) {
			throw new java.lang.IllegalArgumentException("Could not map a position to different elements.");
		} else
			itemMapping.put(position, element);
			
	}
	
	public AbstractSsElement getLegendHeader() {
		return legendHeader;
	}
	
	public List<AbstractSsElement> getLegendItems() {
		List<AbstractSsElement> items = new ArrayList<AbstractSsElement>();
		for (AbstractSsElement el : itemMapping.values())
			if (!items.contains(el))
				items.add(el);
		return items;
	}

	@Override
	public AbstractSsElement getElementFor(CellSpaceInformation position) {
		if ((headerPosition != null) && (headerPosition.equals(position)) )
			return legendHeader;
		else 
			return itemMapping.get(position);
	}

	@Override
	public Boolean hasMappingFor(CellSpaceInformation position) {
		return ((headerPosition != null) && (headerPosition.equals(position)) || itemMapping.containsKey(position));
	}
	
	@Override
	public List<AbstractSsElement> getAllElements() {
		List<AbstractSsElement> allElements = new ArrayList<AbstractSsElement>();
		for (AbstractSsElement el : itemMapping.values())
			if (!allElements.contains(el))
				allElements.add(el);
		if (legendHeader != null)
			allElements.add(legendHeader);
		return allElements;
	}

	@Override
	public List<CellSpaceInformation> getPositionFor(AbstractSsElement elem) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		
		for (Entry<CellSpaceInformation, AbstractSsElement> tuple : itemMapping.entrySet())
			if (tuple.getValue().equals(elem) )
					positions.add(tuple.getKey());
		
		if ((legendHeader != null) && (legendHeader.equals(elem)) )
			positions.add(headerPosition);
		
		return positions;
	}

	@Override
	public Boolean hasMappingFor(AbstractSsElement elem) {
		boolean positionFound = false;
		
		if ((legendHeader != null ) && (legendHeader.equals(elem)) )
			positionFound = true;
		else {
			for (Entry<CellSpaceInformation, AbstractSsElement> tuple : itemMapping.entrySet())
				if (tuple.getValue().equals(elem) )
						positionFound = true;
		}
		return positionFound;
	}
	
	@Override
	public List<CellSpaceInformation> getAllPositions() {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>(itemMapping.keySet());
		if (headerPosition != null)
			positions.add(headerPosition);
		return positions;
	}
	
	public sally.LegendMappingMsg getProtoBufRepresentation(int id) {
		sally.LegendMappingMsg.Builder msgBuilder = sally.LegendMappingMsg.newBuilder();
		msgBuilder.setLegendId(id);
		if (legendHeader != null)
			msgBuilder.setHeaderElementId(legendHeader.getId());
		if (headerPosition != null)
			msgBuilder.setHeaderPosition(headerPosition.getProtoBufRepresentation());
		
		for (Entry<CellSpaceInformation, AbstractSsElement> itemPos : itemMapping.entrySet())
			msgBuilder.addElementPositions(sally.ElementMappingMsg.newBuilder().setPosition(itemPos.getKey().getProtoBufRepresentation()).setAbsElemId(itemPos.getValue().getId()) );
		
		return msgBuilder.build();
	}

}
