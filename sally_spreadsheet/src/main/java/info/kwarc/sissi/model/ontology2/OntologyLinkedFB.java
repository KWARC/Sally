package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;
import info.kwarc.sissi.model.document.spreadsheet.FunctionalBlock;
import info.kwarc.sissi.model.document.spreadsheet.LegendProductEntry;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;


public class OntologyLinkedFB implements OntologyLinkedStructure {

	private static String propertyURIValueFor = "http://www.kwarc.info/sally/asm#value-for";
	private static String propertyURIPartOfFunctionalBlock = "http://www.kwarc.info/sally/asm#partOfFunctionalBlock";
	private static String propertyURIFunctionalInstance = "http://www.kwarc.info/sally/asm#FunctionalInstance";
	private static String propertyURIFunctionalBlock = "http://www.kwarc.info/sally/asm#FunctionalBlock";

	String documentURI, ontoURI;
	FunctionalBlock fb;
	Map<AbstractSsElement, String> elementToURI;
	Map<String, AbstractSsElement> uriToElement;

	public OntologyLinkedFB(String documentURI, String ontoURI, FunctionalBlock fb) {
		this.documentURI = documentURI;
		this.ontoURI = ontoURI;
		this.fb = fb;
		elementToURI = new HashMap<AbstractSsElement, String>();
		uriToElement = new HashMap<String, AbstractSsElement>();

		int counter = 1;
		for (AbstractSsElement el : fb.getAllEntries()) {
			String elemID = documentURI + "/fb/"+fb.getId()+"/value-" + (new Integer(counter).toString());
			elementToURI.put(el, elemID);
			uriToElement.put(elemID, el);
			counter++;
		}
	}

	@Override
	public String getMainURI() {
		return ontoURI;
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

	@Override
	public void exportIntoModel(Model model, OntologyMapping mapping) {

		Property propertyValueFor = model.createProperty(propertyURIValueFor);
		Property propertyPartOfFunctionalBlock = model.createProperty(propertyURIPartOfFunctionalBlock);
		// create the resource
		Resource propertyFunctionalInstance = model.createResource(propertyURIFunctionalInstance);

		Resource functionalBlockResource = model.createResource(documentURI+"/fb/"+fb.getId());
		functionalBlockResource.addProperty(RDF.type, model.createResource(propertyURIFunctionalBlock));

		for (AbstractSsElement fbValue : fb.getAllEntries()) {
			Resource ontoValue = model.createResource(elementToURI.get(fbValue));
			//ontoValue.addProperty(RDF.type, ontologyFunction);
			ontoValue.addProperty(RDF.type, propertyFunctionalInstance);
			ontoValue.addProperty(RDF.value, fbValue.getValue());
			ontoValue.addProperty(propertyPartOfFunctionalBlock, functionalBlockResource);

			for (LegendProductEntry entry : fb.getLegendElementsFor(fbValue)) {

				for (AbstractSsElement entryElement : entry.getLegendTuple()) {
					if (mapping.getURI(entryElement) == null || mapping.getURI(entryElement).isEmpty() )
						throw new java.lang.IllegalArgumentException("Functional block depends on legends that are not linked to the ontology.");
					ontoValue.addProperty(propertyValueFor, model.getResource( mapping.getURI(entryElement) ));
				}
			}
		}
	}

}
