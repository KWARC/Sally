package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class FunctionalBlockMapping extends Mapping {
	Map<CellSpaceInformation, AbstractSsElement> absMapping;
	Map<CellSpaceInformation, LegendProductEntry> domainMapping;
	LegendProduct domain;
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((absMapping == null) ? 0 : absMapping.hashCode());
		result = prime * result + ((domain == null) ? 0 : domain.hashCode());
		result = prime * result
				+ ((domainMapping == null) ? 0 : domainMapping.hashCode());
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
		FunctionalBlockMapping other = (FunctionalBlockMapping) obj;
		if (absMapping == null) {
			if (other.absMapping != null)
				return false;
		} else if (!absMapping.equals(other.absMapping))
			return false;
		if (domain == null) {
			if (other.domain != null)
				return false;
		} else if (!domain.equals(other.domain))
			return false;
		if (domainMapping == null) {
			if (other.domainMapping != null)
				return false;
		} else if (!domainMapping.equals(other.domainMapping))
			return false;
		return true;
	}

	public FunctionalBlockMapping(
			LegendProduct domain,
			Map<CellSpaceInformation, AbstractSsElement> absMapping,
			Map<CellSpaceInformation, LegendProductEntry> domainMapping) {
		super();
		
		if (!absMapping.keySet().equals(domainMapping.keySet()))
			throw new java.lang.IllegalArgumentException("absMapping and domainMapping have different domains.");
		
		this.domain = domain;
		this.absMapping = absMapping;
		for (LegendProductEntry domainEntry : domainMapping.values())
			if (!domain.isValidEntry(domainEntry))
				throw new java.lang.IllegalArgumentException("Invalid domain entry in  domain-mapping.");
		this.domainMapping = domainMapping;
	}
	
	public LegendProduct getDomain() {
		return domain;
	}

	public void addMapping(CellSpaceInformation position, AbstractSsElement absElem, LegendProductEntry domainElem) {
		if (absMapping.containsKey(position)) {
			throw new java.lang.IllegalArgumentException("Could not map a position to different elements.");
		} else {
			absMapping.put(position, absElem);
			domainMapping.put(position, domainElem);
		}
	}
	
	public LegendProductEntry getDomainEntryFor(CellSpaceInformation position) {
		return domainMapping.get(position);
	}
	
	public Boolean hasDomainMappingFor(CellSpaceInformation position) {
		return domainMapping.containsKey(position);
	}

	@Override
	public AbstractSsElement getElementFor(CellSpaceInformation position) {
		return absMapping.get(position);
	}

	@Override
	public Boolean hasMappingFor(CellSpaceInformation position) {
		return absMapping.containsKey(position);
	}
	
	@Override
	public List<AbstractSsElement> getAllElements() {
		List<AbstractSsElement> items = new ArrayList<AbstractSsElement>();
		for (AbstractSsElement el : absMapping.values())
			if (!items.contains(el))
				items.add(el);
		return items;
	}

	@Override
	public List<CellSpaceInformation> getPositionFor(AbstractSsElement elem) {
		List<CellSpaceInformation> positions = new ArrayList<CellSpaceInformation>();
		
		for (Entry<CellSpaceInformation, AbstractSsElement> tuple : absMapping.entrySet())
			if (tuple.getValue().equals(elem) )
					positions.add(tuple.getKey());
		
		return positions;
	}

	@Override
	public Boolean hasMappingFor(AbstractSsElement elem) {
		boolean positionFound = false;
		
		for (Entry<CellSpaceInformation, AbstractSsElement> tuple : absMapping.entrySet())
			if (tuple.getValue().equals(elem) )
					positionFound = true;
		
		return positionFound;
	}

	@Override
	public List<CellSpaceInformation> getAllPositions() {
		return new ArrayList<CellSpaceInformation>(absMapping.keySet());
	}
	
	public sally.FunctionalBlockMappingMsg getProtoBufRepresentation(int id) {
		sally.FunctionalBlockMappingMsg.Builder msgBuilder = sally.FunctionalBlockMappingMsg.newBuilder();
		msgBuilder.setFbId(id);
		msgBuilder.setDomain(domain.getProtoBufRepresentation());
		
		for (Entry<CellSpaceInformation, AbstractSsElement> itemPos : absMapping.entrySet())
			msgBuilder.addElementMapping(sally.ElementMappingMsg.newBuilder().setPosition(itemPos.getKey().getProtoBufRepresentation()).setAbsElemId(itemPos.getValue().getId()) );
		
		for (Entry<CellSpaceInformation, LegendProductEntry> domainPos : domainMapping.entrySet())
			msgBuilder.addDomainMapping(sally.DomainMappingMsg.newBuilder().setPosition(domainPos.getKey().getProtoBufRepresentation()).setDomainElement(domainPos.getValue().getProtoBufRepresentation()) );
		
		return msgBuilder.build();
	}

}
