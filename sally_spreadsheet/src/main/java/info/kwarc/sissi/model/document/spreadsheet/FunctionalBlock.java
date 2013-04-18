package info.kwarc.sissi.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class FunctionalBlock extends AbstractStructure  {
	
	LegendProduct domain;
	Map<LegendProductEntry, AbstractSsElement> function;
	
	public FunctionalBlock(int id, LegendProduct domain) {
		super(id);
		this.domain = domain;
		function = new HashMap<LegendProductEntry, AbstractSsElement>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((domain == null) ? 0 : domain.hashCode());
		result = prime * result
				+ ((function == null) ? 0 : function.hashCode());
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
		FunctionalBlock other = (FunctionalBlock) obj;
		if (domain == null) {
			if (other.domain != null)
				return false;
		} else if (!domain.equals(other.domain))
			return false;
		if (function == null) {
			if (other.function != null)
				return false;
		} else if (!function.equals(other.function))
			return false;
		return true;
	}

	public void addEntry(LegendProductEntry entry, AbstractSsElement value) {
		if (domain.isValidEntry(entry))
			function.put(entry, value);
	}
	
	public AbstractSsElement getEntry(LegendProductEntry entry) {
		if (function.containsKey(entry))
			return function.get(entry);
		else
			return null;
	}
	
	public List<AbstractSsElement> getAllEntries() {
		return new ArrayList<AbstractSsElement>(function.values());
	}
	
	public List<LegendProductEntry> getLegendElementsFor(AbstractSsElement element) {
		List<LegendProductEntry> resultList = new ArrayList<LegendProductEntry>();
		for (Entry<LegendProductEntry, AbstractSsElement> entry : function.entrySet()) {
			if (entry.getValue().equals(element))
				resultList.add(entry.getKey());
		}
		return resultList;
	}
	
	public List<LegendProductEntry> getAllLegendElements() {
		return new ArrayList<LegendProductEntry>(function.keySet());
	}
	
	public LegendProduct getDomainLegends() {
		return domain;
	}
	
	public sally.FunctionalBlockMsg getProtoBufRepresentation() {
		sally.FunctionalBlockMsg.Builder msgBuilder = sally.FunctionalBlockMsg.newBuilder().setId(getId()).setDomain(domain.getProtoBufRepresentation());
		for (Entry<LegendProductEntry, AbstractSsElement> entry : function.entrySet()) {
			msgBuilder.addEntry( sally.FBEntryMsg.newBuilder().setDomainElem(entry.getKey().getProtoBufRepresentation()).setAbsElemId(entry.getValue().getId()).build() );
		}
		
		return msgBuilder.build();
	}

}
