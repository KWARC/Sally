package info.kwarc.sally.spreadsheet3.extraction;

import java.util.ArrayList;
import java.util.List;

/**
 * A class to provide information about found areas and their relations.
 * @author cliguda
 *
 */
public class ParsingResult {
	List<AEResults> aeResults;
	List<AffiliationInformation> affInfos;
	
	public ParsingResult() {
		super();
		this.aeResults = new ArrayList<AEResults>();
		this.affInfos = new ArrayList<AffiliationInformation>();
	}

	public void addAEResult(AEResults aeResults) {
		this.aeResults.add(aeResults);
	}
	
	public void addAllAffiliationInformation(List<AffiliationInformation> affInfos) {
		this.affInfos.addAll(affInfos);
	}
	
	public List<AEResults> getAeResults() {
		return aeResults;
	}

	public List<AffiliationInformation> getAffInfos() {
		return affInfos;
	}
	
}
