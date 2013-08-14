package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class CellTuple {
	
	List<CellSpaceInformation> tuple;

	public CellTuple(List<CellSpaceInformation> tuple) {
		super();
		this.tuple = tuple;
	}
	
	public List<CellSpaceInformation> getTuple() {
		return new ArrayList<CellSpaceInformation>(tuple);
	}
	
	public void setTuple(List<CellSpaceInformation> tuple) {
		this.tuple = tuple; 
	}
	
	public int getSize() {
		return tuple.size();
	}
	
	public Boolean contains(CellSpaceInformation position) {
		return tuple.contains(position);
	}

	public String toString() {
		String strRep = "[";
		for (CellSpaceInformation p : tuple)
			strRep = strRep + p.toString() + ",";
		if (strRep.endsWith(","))
			strRep = strRep.substring(0, strRep.length()-1);
		strRep = strRep + "]";
		return strRep;
	}

}
