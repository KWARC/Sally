package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;

public class StructureCreateParameter {
	
	public enum DataParameter {
		AllDiff,
		SameStringSameElement,
		SameContentSameElement
	}
	
	DataParameter dataParam = DataParameter.AllDiff;
	List<Integer> connectToAll = new ArrayList<Integer>();
	
	public StructureCreateParameter() {
		super();
	}

	public DataParameter getDataParam() {
		return dataParam;
	}

	public void setDataParam(DataParameter dataParam) {
		this.dataParam = dataParam;
	}

	public List<Integer> getConnectToAll() {
		return connectToAll;
	}

	public void setConnectToAll(List<Integer> connectToAll) {
		this.connectToAll = connectToAll;
	}
	
}
