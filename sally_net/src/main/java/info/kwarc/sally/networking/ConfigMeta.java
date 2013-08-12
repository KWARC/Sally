package info.kwarc.sally.networking;

public class ConfigMeta {
	public String id;
	public String url;
	public String description;
	
	public ConfigMeta(String id, String url, String description) {
		this.id = id;
		this.url = url;
		this.description = description;
	}

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public String getUrl() {
		return url;
	}

	public void setUrl(String url) {
		this.url = url;
	}

	public String getDescription() {
		return description;
	}

	public void setDescription(String description) {
		this.description = description;
	}
	
	
}
