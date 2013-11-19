package info.kwarc.sally.sharejs;

public abstract class AbstractSnapshot {
	protected long version;
	String collection;
	String fileName;

	public AbstractSnapshot(long version, String collection, String fileName) {
		this.version = version;
		this.collection = collection;
		this.fileName = fileName;
	}
	
	public String getCollection() {
		return collection;
	}
	
	public String getFileName() {
		return fileName;
	}
	
	public long getVersion() {
		return version;
	}
	
}
