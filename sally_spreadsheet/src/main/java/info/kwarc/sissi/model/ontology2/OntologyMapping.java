package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;
import info.kwarc.sissi.model.document.spreadsheet.AbstractStructure;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

public class OntologyMapping {
	Map<AbstractSsElement, String> elementToURI;
	Map<String, AbstractSsElement> uriToElement;
	Map<AbstractStructure, OntologyLinkedStructure> mappings;
	
	public OntologyMapping() {
		elementToURI = new HashMap<AbstractSsElement, String>();
		uriToElement = new HashMap<String, AbstractSsElement>();
		mappings = new HashMap<AbstractStructure,OntologyLinkedStructure>();
	}
	
	public String getURI(AbstractSsElement el) {
		return elementToURI.get(el);
	}

	public AbstractSsElement getElement(String uri) {
		return uriToElement.get(uri);
	}
	
	public void addMapping(OntologyLinkedStructure mapping, AbstractStructure structure) {
		for (String uri : mapping.getAllURIs()) {
			if (uriToElement.containsKey(uri) && !uriToElement.get(uri).equals(mapping.getElement(uri)) )
				throw new java.lang.IllegalArgumentException("Same URI with different abstract element already existing.");
			if (elementToURI.containsKey(mapping.getElement(uri)) && !elementToURI.get(mapping.getElement(uri)).equals(uri) )
				throw new java.lang.IllegalArgumentException("Same element with different URI already existing.");
		}
		mappings.put(structure,  mapping);
		for (String uri : mapping.getAllURIs()) {
			uriToElement.put(uri, mapping.getElement(uri));
			elementToURI.put(mapping.getElement(uri), uri);
		}
	}
	
	public Model getRDFModel() {
		// create an empty Model
		Model model = ModelFactory.createDefaultModel();
		model.setNsPrefix("asm", "http://www.kwarc.info/sally/asm#");
		model.setNsPrefix("csm", "http://www.kwarc.info/sally/csm#");
		for (OntologyLinkedStructure map : mappings.values())
			map.exportIntoModel(model, this);
	
		return model;
	}
	
	public List<AbstractStructure> getAllStructures() {
		return new ArrayList<AbstractStructure>(mappings.keySet());
	}
	
	public OntologyLinkedStructure getLinkingFor(AbstractStructure s) {
		return mappings.get(s);
	}
	
}
