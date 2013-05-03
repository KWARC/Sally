package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;

public class AbstractSsModel {
	AbstractDataModel dataModel;
	List<Legend> legends;
	List<FunctionalBlock> functionalBlocks;
	List<LegendProduct> legendDependencies;
	
	public AbstractSsModel() {
		dataModel = new AbstractDataModel();
		legends = new ArrayList<Legend>();
		functionalBlocks = new ArrayList<FunctionalBlock>();
		legendDependencies = new ArrayList<LegendProduct>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((dataModel == null) ? 0 : dataModel.hashCode());
		result = prime
				* result
				+ ((functionalBlocks == null) ? 0 : functionalBlocks.hashCode());
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
		AbstractSsModel other = (AbstractSsModel) obj;
		if (dataModel == null) {
			if (other.dataModel != null)
				return false;
		} else if (!dataModel.equals(other.dataModel))
			return false;
		if (functionalBlocks == null) {
			if (other.functionalBlocks != null)
				return false;
		} else if (!functionalBlocks.equals(other.functionalBlocks))
			return false;
		if (legends == null) {
			if (other.legends != null)
				return false;
		} else if (!legends.equals(other.legends))
			return false;
		return true;
	}

	public void addLegend(Legend legend) {
		legends.add(legend);
	}
	
	public void addFunctionalBlock(FunctionalBlock fb) {
		functionalBlocks.add(fb);
	}
	
	public void addLegendDependency(LegendProduct dependency) {
		legendDependencies.add(dependency);
	}
	
	public List<AbstractSsElement> getDependeningLegendItems(AbstractSsElement element, Legend legend) {
		List<LegendProductEntry> relevantEntries = new ArrayList<LegendProductEntry>();
		for (LegendProduct legendDependency : legendDependencies) {
			relevantEntries.addAll(legendDependency.getEntryFor(legend, element));
		}
		
		List<AbstractSsElement> dependingItems = new ArrayList<AbstractSsElement>();
		for (LegendProductEntry entry : relevantEntries)
			for (AbstractSsElement ele: entry.getLegendTuple())
				if (!dependingItems.contains(ele))
					dependingItems.add(ele);
		return dependingItems;
	}
	
	public AbstractDataModel getDataModel() {
		return dataModel;
	}

	public List<Legend> getLegends() {
		return new ArrayList<Legend>(legends);
	}

	public List<FunctionalBlock> getFunctionalBlocks() {
		return new ArrayList<FunctionalBlock>(functionalBlocks);
	}
	
	public void removeLegend(Legend l) {
		legends.remove(l);
	}
	
	public void removeFB(FunctionalBlock fb) {
		functionalBlocks.remove(fb);
	}
	
	public Legend getLegendById(int id) {
		for (Legend l : legends)
			if (l.getId() == id)
				return l;
		return null;
	}
	
	public FunctionalBlock getFBById(int id) {
		for (FunctionalBlock fb : functionalBlocks)
			if (fb.getId() == id)
				return fb;
		return null;
	}
	
	public sally.AbstractSpreadsheetMsg getProtoBufRepresentation() {
		sally.AbstractSpreadsheetMsg.Builder msgBuilder = sally.AbstractSpreadsheetMsg.newBuilder();
		msgBuilder.setElements(dataModel.getProtoBufRepresentation());
		           
		for (Legend legend : legends)
			msgBuilder.addLegends(legend.getProtoBufRepresentation());
		
		
		for (FunctionalBlock fb : functionalBlocks)
			msgBuilder.addFunctionalBlocks(fb.getProtoBufRepresentation());
		
		return msgBuilder.build();
	}
	
}
