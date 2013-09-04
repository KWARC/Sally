package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

class OntologyRelationLink {
	String uri;
	final String mathMLTemplate;
	List<OntologyBlockLink> blockLinks;
	
	public OntologyRelationLink(String uri, String mathMLTemplate, List<OntologyBlockLink> blockLinks) {
		super();
		this.uri = uri;
		this.mathMLTemplate = mathMLTemplate;
		this.blockLinks = new ArrayList<OntologyBlockLink>(blockLinks);
	}

	public String getUri() {
		return uri;
	}
	
	public String getRelationInterpretation(List<String> values) {
		
		if (blockLinks.size() != values.size())
			throw new java.lang.IllegalArgumentException("Relation size is different than the number of arguments.");
		
		String mathMLInterpretation = mathMLTemplate;
		for (int i = 0; i < values.size(); i++) {
			mathMLInterpretation = mathMLInterpretation.replace("<rvar num=\"" + (i+1) + "\"/>", blockLinks.get(i).getValueInterpretation(values.get(i)));
		}
		
		return mathMLInterpretation;
	}
	
}
