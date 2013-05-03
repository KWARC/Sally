package info.kwarc.sally.model.document.spreadsheet;

import java.util.List;

public abstract class Mapping {
	
	public abstract AbstractSsElement getElementFor(CellSpaceInformation position);
	
	public abstract Boolean hasMappingFor(CellSpaceInformation position);
	
	public abstract List<AbstractSsElement> getAllElements();
	
	public abstract List<CellSpaceInformation> getPositionFor(AbstractSsElement elem);
	
	public abstract Boolean hasMappingFor(AbstractSsElement elem);
	
	public abstract List<CellSpaceInformation> getAllPositions();


}
