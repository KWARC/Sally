package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class OntologyRelationLink {
	String uri;
	final String mlTemplate;
	List<OntologyBlockLink> blockLinks;
	BuilderML builderML;
	
	public OntologyRelationLink(String uri, String mlTemplate, List<OntologyBlockLink> blockLinks, BuilderML builderML) {
		super();
		this.uri = uri;
		this.mlTemplate = mlTemplate;
		this.blockLinks = new ArrayList<OntologyBlockLink>(blockLinks);
		this.builderML = builderML;
	}

	public String getUri() {
		return uri;
	}
	
	public String getRelationInterpretation(List<String> values) {
		
		if (blockLinks.size() != values.size())
			throw new java.lang.IllegalArgumentException("Relation size is different than the number of arguments.");
		
		String mlInterpretation = mlTemplate;
		for (int i = 0; i < values.size(); i++) {
			mlInterpretation = mlInterpretation.replace(builderML.getVIVaribale(i+1), blockLinks.get(i).getValueInterpretation(values.get(i)));
		}
		
		return mlInterpretation;
	}
	
}
