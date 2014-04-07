package info.kwarc.sally.spreadsheet3.model;

import java.util.ArrayList;
import java.util.List;

public class CellTuple {
	
	List<CellSpaceInformation> tuple;

	public CellTuple(List<CellSpaceInformation> tuple) {
		super();
		this.tuple = new ArrayList<CellSpaceInformation>(tuple);
	}
	
	public CellTuple(Sally.CellTupleMsg msg) {
		tuple = new ArrayList<CellSpaceInformation>();
		for (Sally.CellSpaceInformationMsg cellMsg : msg.getTupleList())
			tuple.add(new CellSpaceInformation(cellMsg));
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((tuple == null) ? 0 : tuple.hashCode());
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
		CellTuple other = (CellTuple) obj;
		if (tuple == null) {
			if (other.tuple != null)
				return false;
		} else if (!tuple.equals(other.tuple))
			return false;
		return true;
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
	
	public Sally.CellTupleMsg serialize() {
		Sally.CellTupleMsg.Builder msg = Sally.CellTupleMsg.newBuilder();
		for (CellSpaceInformation pos : this.tuple)
			msg.addTuple(pos.serialize());
		
		return msg.build();
	}

}
