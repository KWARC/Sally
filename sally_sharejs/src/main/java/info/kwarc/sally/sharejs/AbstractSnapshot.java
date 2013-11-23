package info.kwarc.sally.sharejs;

public abstract class AbstractSnapshot {
	protected long version;
	String collection;
	String fileName;

	public AbstractSnapshot() {
	}
	
	public AbstractSnapshot setCollection(String collection) {
		this.collection = collection;
		return this;
	}
	
	public AbstractSnapshot setFileName(String fileName) {
		this.fileName = fileName;
		return this;
	}
	
	public AbstractSnapshot setVersion(long version) {
		this.version = version;
		return this;
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
	
	public abstract void setSnapshot(String otType, String data);
	
	
}
