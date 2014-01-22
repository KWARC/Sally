package info.kwarc.sally.sharejs;

import java.util.HashMap;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;

public class DocumentCreateRequest implements IDocumentOp {
	@JsonIgnore
	String type;
	@JsonIgnore
	String data;
	
	public String getType() {
		return type;
	}
	
	public DocumentCreateRequest setType(String type) {
		this.type = type;
		return this;
	}
	
	public String getData() {
		return data;
	}
	
	public DocumentCreateRequest setData(String data) {
		this.data = data;
		return this;
	}
	
	@JsonProperty
	public Object getCreate() {
		HashMap <String, String> createOp = new HashMap<String, String>();
		createOp.put("type", type);
		createOp.put("data", data);
		return createOp;
	}
}
