package info.kwarc.sissi.model.ontology2;

import info.kwarc.sissi.model.document.spreadsheet.AbstractSsElement;
import info.kwarc.sissi.model.document.spreadsheet.Legend;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;
import com.hp.hpl.jena.vocabulary.RDFS;

public class OntologyLinkedLegendSubType extends OntologyLinkedLegend {
	private static String propertyURILegendInstance = "http://www.kwarc.info/sally/asm#LegendInstance";
	private static String propertyURILegendBlock = "http://www.kwarc.info/sally/asm#LegendBlock";
	private static String propertyURIPartOfLagendBlock = "http://www.kwarc.info/sally/asm#partOfLegendBlock";
	String itemPrefix;
	
	public OntologyLinkedLegendSubType(String documentURI, String uri, String itemprefix, Legend l) {
		super(documentURI, uri);
		this.itemPrefix = itemprefix;
		if (l.getHeader() != null) {
			elementToURI.put(l.getHeader(), uri);
			uriToElement.put(uri,  l.getHeader());
		}
		for (AbstractSsElement el : l.getItems()) {

			String itemURI = itemprefix + el.getValue();
			if (uriToElement.containsKey(itemURI)) {
				int index = 1;
				while (uriToElement.containsKey(itemURI + "-" + (new Integer(index).toString())) )
					index++;
				itemURI = itemURI + "-" + (new Integer(index).toString());
			}
				
			elementToURI.put(el, itemURI);
			uriToElement.put(itemURI, el);
		}
	}
	
	public OntologyLinkedLegendSubType(String documentURI, String uri, Legend l) {
		this(documentURI, uri, documentURI+"/lb/"+l.getId()+"/", l);
	}


	@Override
	public void exportIntoModel(Model model, OntologyMapping mapping) {
		Resource lbResource = model.createResource(itemPrefix);
		lbResource.addProperty(RDF.type, model.createResource(propertyURILegendBlock));
		
		// create the resource
		Resource legendheader = model.createResource(ontologyURI);
		
		if (uriToElement.containsKey(documentURI) && !uriToElement.get(documentURI).getValue().isEmpty()) {
			legendheader.addProperty(RDFS.label, uriToElement.get(documentURI).getValue());
		}
		for (String uri : uriToElement.keySet()) {
			if (!uri.equals(documentURI)) {
				Resource item = model.createResource(uri);
				item.addProperty(RDF.type, model.createResource(propertyURILegendInstance));
				item.addProperty(model.createProperty(propertyURIPartOfLagendBlock), lbResource);
				item.addProperty(RDFS.subClassOf, legendheader);
				item.addProperty(RDFS.label, uriToElement.get(uri).getValue());
			}
		}
	}
	
}
