package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;

import java.util.List;

import com.hp.hpl.jena.rdf.model.Model;

public interface OntologyLinkedStructure {
	
	public void exportIntoModel(Model model, OntologyMapping mapping);
	
	public String getURI(AbstractSsElement el);

	public AbstractSsElement getElement(String uri);

	public List<String> getAllURIs();
	
	public String getMainURI();

}
