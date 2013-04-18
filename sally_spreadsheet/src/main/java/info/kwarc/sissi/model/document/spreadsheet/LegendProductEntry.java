package info.kwarc.sissi.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;

public class LegendProductEntry {
	List<Legend> legends;
	List<AbstractSsElement> legendTuple;
	

	public LegendProductEntry(List<Legend> legends, List<AbstractSsElement> legendTuple) {
		super();
		boolean valid = true;
		/*if (legends.size() != legendTuple.size()) {
			valid = false;
		} else {
			for (int i = 0; i < legends.size(); i++)
				if (!legends.get(i).contains(legendTuple.get(i)))
					valid = false;
		}*/
		
		for (AbstractSsElement e : legendTuple) {
			boolean found = false;
			for (int i = 0; (i < legends.size()) && !found; i++) {
				if (legends.get(i).contains(e))
					found = true;
			}
			if (!found)
				valid = false;
		}
		
		if(valid) {
			this.legends = legends;
			this.legendTuple = legendTuple;
		} else
			throw new java.lang.IllegalArgumentException("Invalid arguments.");
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((legendTuple == null) ? 0 : legendTuple.hashCode());
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
		LegendProductEntry other = (LegendProductEntry) obj;
		if (legendTuple == null) {
			if (other.legendTuple != null)
				return false;
		} else if (!legendTuple.equals(other.legendTuple))
			return false;
		if (legends == null) {
			if (other.legends != null)
				return false;
		} else if (!legends.equals(other.legends))
			return false;
		return true;
	}

	public List<AbstractSsElement> getLegendTuple() {
		return new ArrayList<AbstractSsElement>(legendTuple);
	}
	
	public List<Legend> getLegends() {
		return new ArrayList<Legend>(legends);
	}
	
	public boolean isPartOfTuple(Legend legend, AbstractSsElement element) {
		if (!legend.contains(element))
			throw new java.lang.IllegalArgumentException("The element is not part of the given legend");
		
		boolean found = false;
		
		for (int i = 0; (i < legends.size()) && !found; i++) {
			if (legends.get(i).equals(legend) && legendTuple.get(i).equals(element))
				found = true;
			
		}
		return found;
	}
	
	public void changeCPTuple(List<AbstractSsElement> newTuple) {
		boolean valid = true;
		if (legends.size() != newTuple.size()) {
			valid = false;
		} else {
			for (int i = 0; i < legends.size(); i++)
				if (!legends.get(i).contains(newTuple.get(i)))
					valid = false;
		}
		
		if(valid) {
			this.legendTuple = newTuple;
		} else
			throw new java.lang.IllegalArgumentException("Invalid arguments for newTuple.");
	}
	
	public sally.LegendProductEntryMsg getProtoBufRepresentation() {
		sally.LegendProductEntryMsg.Builder msgBuilder = sally.LegendProductEntryMsg.newBuilder();
		for (Legend l : legends)
			msgBuilder.addLegends(l.getId());
		
		for (AbstractSsElement e : legendTuple)
			msgBuilder.addElements(e.getId());
	
		return msgBuilder.build();
	}
}
