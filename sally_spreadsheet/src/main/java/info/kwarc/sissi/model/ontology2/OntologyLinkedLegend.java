package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public abstract class OntologyLinkedLegend implements OntologyLinkedStructure {
	String documentURI;
	String ontologyURI;
	
	Map<AbstractSsElement, String> elementToURI;
	Map<String, AbstractSsElement> uriToElement;
	
	OntologyLinkedLegend(String documentURI, String ontologyURI) {
		this.documentURI = documentURI;
		this.ontologyURI = ontologyURI;
		
		elementToURI = new HashMap<AbstractSsElement, String>();
		uriToElement = new HashMap<String, AbstractSsElement>();
	}
	
	@Override
	public String getMainURI() {
		return ontologyURI;
	}
	
	@Override
	public String getURI(AbstractSsElement el) {
		return elementToURI.get(el);
	}

	@Override
	public AbstractSsElement getElement(String uri) {
		return uriToElement.get(uri);
	}

	@Override
	public List<String> getAllURIs() {
		return new ArrayList<String>(uriToElement.keySet());
	}
	
	public Boolean setURI(AbstractSsElement el, String uri) {
		if (elementToURI.containsKey(el) && !uriToElement.containsKey(uri)) {
			elementToURI.put(el, uri);
			uriToElement.put(uri, el);
			return true;
		} else
			return false;
	}
	
}
