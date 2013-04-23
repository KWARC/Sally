package info.kwarc.sissi.model.document.cad;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ACMNode {
	String id;
	String url;
	List<ACMNode> children; 
	Map<String, String> properties;
	ACMNode parent;

	public String getId() {
		return id;
	}
	
	public ACMNode(String id) {
		this.id = id;
		this.url = null;
		children = new ArrayList<ACMNode>();
		properties = new HashMap<String, String>();
		parent = null;
	}
	
	public void setParent(ACMNode parent) {
		this.parent = parent;
	}
	
	public ACMNode getParent() {
		return parent;
	}
	
	public List<ACMNode> getChildren() {
		return children;
	}
	
	public Map<String, String> getProperties() {
		return properties;
	}

	public static ACMNode createNode(String id) {
		return new ACMNode(id);
	}
	
	public ACMNode addChild(ACMNode child) {
		children.add(child);
		child.setParent(this);
		return this;
	}
	
	public ACMNode addProperty(String uri, String value) {
		properties.put(uri, value);
		return this;
	}
};
