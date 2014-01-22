package info.kwarc.sally.spreadsheet3.extraction;

import java.util.List;

public class AffiliationInformation {
	int id;
	List<Integer> affiliatedIds;
	
	public AffiliationInformation(int id, List<Integer> affiliatedIds) {
		super();
		this.id = id;
		this.affiliatedIds = affiliatedIds;
	}

	public int getId() {
		return id;
	}

	public List<Integer> getAffiliatedIds() {
		return affiliatedIds;
	}
	
	@Override
	public String toString() {
		String result = "ID: " + id + " -> ";
		for (Integer i : affiliatedIds)
			result += i + " ";
		return result;
	}
	
}