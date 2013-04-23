package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;
import info.kwarc.sissi.model.document.spreadsheet.FunctionalBlock;
import info.kwarc.sissi.model.document.spreadsheet.LegendProductEntry;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;


public class OntologyLinkedFB implements OntologyLinkedStructure {

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

		Resource documentResource = model.createResource(documentURI);
		Resource functionalBlockResource = model.createResource(documentURI+"/fb/"+fb.getId());
		
		functionalBlockResource.addProperty(RDF.type, model.createResource(ASM.FunctionalBlock));
		functionalBlockResource.addProperty(ASM.partOfFile, documentResource);
		functionalBlockResource.addProperty(IM.ontologyURI, model.createResource(ontoURI));
		
		for (AbstractSsElement fbValue : fb.getAllEntries()) {
			Resource ontoValue = model.createResource(elementToURI.get(fbValue));
			ontoValue.addProperty(RDF.type, ASM.FunctionalInstance);
			ontoValue.addProperty(RDF.value, fbValue.getValue());
			ontoValue.addProperty(ASM.partOfFunctionalBlock, functionalBlockResource);

			for (LegendProductEntry entry : fb.getLegendElementsFor(fbValue)) {

				for (AbstractSsElement entryElement : entry.getLegendTuple()) {
					if (mapping.getURI(entryElement) == null || mapping.getURI(entryElement).isEmpty() )
						throw new java.lang.IllegalArgumentException("Functional block depends on legends that are not linked to the ontology.");
					ontoValue.addProperty(ASM.valueOf, model.getResource( mapping.getURI(entryElement) ));
				}
			}
		}
	}

}
