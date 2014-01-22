package info.kwarc.sally.sharejs.text;

import info.kwarc.sally.sharejs.IDocumentOp;

import java.util.ArrayList;
import java.util.List;

import com.fasterxml.jackson.annotation.JsonProperty;

public class TextOp implements IDocumentOp {
	@JsonProperty("v")
	long baseVersion;
	
	@JsonProperty("op")
	List<IBasicTextOp> basicOps;

	
	
	public List<IBasicTextOp> getBasicOps() {
		return basicOps;
	}
	
	public TextOp() {
		basicOps = new ArrayList<IBasicTextOp>();
	}
	
	public long getBaseVersion() {
		return baseVersion;
	}
	
	public TextOp setBaseVersion(long baseVersion) {
		this.baseVersion = baseVersion;
		return this;
	}
	
	public TextOp addBasicTextOp(IBasicTextOp op) {
		basicOps.add(op);
		return this;
	}
	
	public TextOp addSkipOp(int len) {
		return addBasicTextOp(new SkipTextOp(len));
	}

	public TextOp addRemoveOp(int len) {
		return addBasicTextOp(new RemoveTextOp(len));
	}

	public TextOp addInsertOp(String text) {
		return addBasicTextOp(new InsertTextOp(text));
	}
}
