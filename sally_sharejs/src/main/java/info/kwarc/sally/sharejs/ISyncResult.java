package info.kwarc.sally.sharejs;

import info.kwarc.sally.sharejs.text.TextOp;

import java.util.List;

public class ISyncResult {
	long version;
	List<TextOp> op;
	
	public List<TextOp> getOp() {
		return op;
	}
	
	public ISyncResult(long version) {
		this.version= version;
	}
	
	long getVersion() {
		return version;
	}
}
