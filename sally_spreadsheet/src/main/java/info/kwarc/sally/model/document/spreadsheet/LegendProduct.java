package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;

public class LegendProduct {
	
	List<Legend> legends;
	List<LegendProductEntry> entries;
	
	public LegendProduct(List<Legend> legends) {
		if (legends == null)
			throw new java.lang.IllegalArgumentException("Legends is a null pointer.");
		this.legends = legends;
		this.entries = new ArrayList<LegendProductEntry>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((entries == null) ? 0 : entries.hashCode());
		result = prime * result + ((legends == null) ? 0 : legends.hashCode());
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
		LegendProduct other = (LegendProduct) obj;
		if (entries == null) {
			if (other.entries != null)
				return false;
		} else if (!entries.equals(other.entries))
			return false;
		if (legends == null) {
			if (other.legends != null)
				return false;
		} else if (!legends.equals(other.legends))
			return false;
		return true;
	}

	public LegendProductEntry addEntry(List<AbstractSsElement> entry) {
		try {
			LegendProductEntry e = new LegendProductEntry(legends, entry);
			entries.add(e);
			return e;
		} catch (java.lang.IllegalArgumentException ex) {
			System.out.println("Tried to add invalid entry to dependency");
			return null;
		}
	}
	
	public List<LegendProductEntry> getEntryFor(Legend l, AbstractSsElement el) {
		List<LegendProductEntry> relevantEntries = new ArrayList<LegendProductEntry>();
		
		if (l.contains(el)) {
			for (LegendProductEntry entry : entries)
				if (entry.isPartOfTuple(l, el))
					relevantEntries.add(entry);
		}
		
		return relevantEntries;
	}
	
	public List<Legend> getLegends() {
		return new ArrayList<Legend>(legends);
	}
	
	public List<LegendProductEntry> getEntries() {
		return new ArrayList<LegendProductEntry>(entries);
	}
	
	public boolean isValidEntry(LegendProductEntry entry) {
		return legends.equals(entry.getLegends());
	}
	
	public boolean containsLegend(Legend l) {
		return legends.contains(l);
	}
	
	
	public sally.LegendProductMsg getProtoBufRepresentation() {
		sally.LegendProductMsg.Builder msgBuilder = sally.LegendProductMsg.newBuilder();
		for (Legend l : legends)
			msgBuilder.addLegends(l.getId());
		for (LegendProductEntry e : entries)
			msgBuilder.addEntries(e.getProtoBufRepresentation());
	
		return msgBuilder.build();
	}
}
