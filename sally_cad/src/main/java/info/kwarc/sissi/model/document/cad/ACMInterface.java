package info.kwarc.sissi.model.document.cad;

import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.binary.Base64;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.CADNode;
import Sally.CADSemanticData;
import Sally.Parameter;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;
import com.hp.hpl.jena.vocabulary.RDFS;

public class ACMInterface {

	Model model;
	String documentURI;
	String fileURI;
	CADNode rootNode;
	Map<String, CADNode> index;
	Logger log;
	
	public void setDocumentURI(String documentURI) {
		this.fileURI = documentURI;
		this.documentURI = makeValidDocURI(documentURI);
	}
	
	public String getDocumentURI() {
		return documentURI;
	}
	
	public static String makeValidDocURI(String URI) {
		URI = URI.replace(':', '_');
		URI = URI.replace('\\', '_');
		return "file://"+URI;
	}
	
	public static String makeValidNodeURI(String nodeId) {
		nodeId = nodeId.replace(':', '_');
		nodeId = nodeId.replace('\\', '_');
		return nodeId;
	}
	
	public Resource getResource(String documentURI, CADNode node) {
		String nodeID = node.getId();
		nodeID = nodeID.replace(':', '_');
		nodeID = nodeID.replace('\\', '_');
		return model.createResource(documentURI+"/"+nodeID);
	}
	
	Map<String, Integer> props;
	int IDs;
	

	public Model getRDFModel() {
		return serialize(rootNode);
	}
	
	public Model serialize(CADNode node) {
		model.removeAll();
		_serialize(null, node);
		return model;
	}
	
	public CADNode getNodeById(String Id) {
		return index.get(Id);
	}

	private void _serialize(CADNode parent, CADNode node) {
		Resource nodeRes = getResource(documentURI, node);
		if (parent != null) {
			Resource parentRes = getResource(documentURI, parent);
			nodeRes.addProperty(ACM.partOf, parentRes);
			nodeRes.addProperty(ACM.partOfFile, model.createLiteral(fileURI));
		}
		
		nodeRes.addProperty(RDF.type, ACM.CADObject);
		nodeRes.addProperty(RDFS.label, model.createLiteral(node.getId()));

		if (node.hasImUri()) {
			nodeRes.addProperty(IM.ontologyURI, model.createResource(node.getImUri()));
		}
		
		for (Parameter parameter : node.getParametersList()) {
			int currentID; 
			String property = parameter.getKey();
			String value = parameter.getValue();
			
			String hashKey = property+"#"+value;
			if (!props.containsKey(hashKey)) {
				currentID = IDs++;
				props.put(hashKey, currentID);
			} else
				currentID = props.get(hashKey);

			Resource propRes = model.createResource(documentURI+"/prop/"+currentID);
			propRes.addProperty(ACM.hasKey, model.createLiteral(property));
			propRes.addProperty(ACM.hasValue, model.createLiteral(value));
			
			nodeRes.addProperty(ACM.valueOf, propRes);
		}
		
		for (CADNode child : node.getChildrenList()) {
			_serialize(node, child);
		}
	}

	public ACMInterface() {
		this("http://default.cad/uri");
		
	}

	private void _reindex(CADNode node) {
		log.debug("");
		index.put(node.getId(), node);
		for (CADNode child : node.getChildrenList()) {
			_reindex(child);
		}
	}
	
	public void reindex() {
		index.clear();
		_reindex(rootNode);
	}
	
	public void importSemanticData(CADSemanticData semanticData) {
		documentURI = semanticData.getFileName();
		rootNode = semanticData.getRootNode();
		reindex();
	}
	
	public CADSemanticData exportSemanticData() {
		CADSemanticData.Builder builder = CADSemanticData.newBuilder();
		builder.setFileName(documentURI);
		builder.setRootNode(rootNode);
		return builder.build();
	}
	
	public void setRootNode(CADNode rootNode) {
		this.rootNode = rootNode;
	}
	
	public void exportRDFToFile(String fileName) {
		OutputStream file;
		try {
			file = new FileOutputStream(fileName);
			getRDFModel().write(file);
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void exportSemanticDataToFile(String fileName) {
		OutputStream file;
		try {
			file = new FileOutputStream(fileName);
			
			ByteArrayOutputStream so = new ByteArrayOutputStream();
			exportSemanticData().writeTo(so);
			byte[] b = so.toByteArray();
			file.write(Base64.encodeBase64(b));
			file.close();			
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	public void importSemanticDataFile(String fileName) {
		InputStream file;
		try {
			file = new FileInputStream(fileName);
			importSemanticData(CADSemanticData.parseFrom(file));
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	public ACMInterface(String documentURI) {
		model = ModelFactory.createDefaultModel();
		model.setNsPrefix("acm", ACM.getURI());
		model.setNsPrefix("im", IM.getURI());
		index = new HashMap<String, CADNode>();
		props = new HashMap<String, Integer>();
		IDs = 0;
		log = LoggerFactory.getLogger(getClass());
		this.fileURI = documentURI;
		this.documentURI = makeValidDocURI(documentURI);
	}	
}
