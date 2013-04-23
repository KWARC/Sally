package info.kwarc.sissi.model.document.cad;

import java.util.HashMap;
import java.util.Map;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;
import com.hp.hpl.jena.vocabulary.RDFS;

public class ACMInterface {

	Model model;
	
	public Resource getResource(String documentURI, ACMNode node) {
		return model.createResource(documentURI+"/"+node.getId());
	}
	
	Map<String, Integer> props;
	int IDs;
	

	public Model serialize(String documentURI, ACMNode node) {
		model.removeAll();
		_serialize(documentURI, node);
		return model;
	}

	private void _serialize(String documentURI, ACMNode node) {
		Resource nodeRes = getResource(documentURI, node);
		if (node.getParent() != null) {
			Resource parentRes = getResource(documentURI, node.getParent());
			nodeRes.addProperty(ACM.partOf, parentRes);
			nodeRes.addProperty(ACM.partOfFile, documentURI);
		}
		
		nodeRes.addProperty(RDF.type, ACM.CADObject);
		
		for (String property : node.getProperties().keySet()) {
			int currentID; 
			String value = node.getProperties().get(property);
			String hashKey = property+"#"+value;
			if (!props.containsKey(hashKey)) {
				currentID = IDs++;
				props.put(hashKey, currentID);
			} else
				currentID = props.get(hashKey);

			Resource propRes = model.createResource(documentURI+"/prop/"+currentID);
			propRes.addProperty(RDFS.label, value);
			propRes.addProperty(IM.ontologyURI, model.createResource(property));
			
			nodeRes.addProperty(ACM.valueOf, propRes);
		}
		
		for (ACMNode child : node.getChildren()) {
			_serialize(documentURI, child);
		}
	}

	
	public ACMInterface() {
		model = ModelFactory.createDefaultModel();
		model.setNsPrefix("acm", ACM.getURI());
		model.setNsPrefix("im", IM.getURI());
		props = new HashMap<String, Integer>();
		IDs = 0;
	}

	public Model getRDFModel(ACMNode root) {
		
		return model;
	}
	
}
