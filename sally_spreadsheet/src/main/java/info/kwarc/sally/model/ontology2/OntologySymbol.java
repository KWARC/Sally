package info.kwarc.sally.model.ontology2;

public class OntologySymbol {
	String name, id, description, descriptionLong;

	public OntologySymbol(String name, String id) {
		super();
		this.name = name;
		this.id = id;
	}

	public String getDescription() {
		return description;
	}

	public void setDescription(String description) {
		this.description = description;
	}

	public String getDescriptionLong() {
		return descriptionLong;
	}

	public void setDescriptionLong(String descriptionLong) {
		this.descriptionLong = descriptionLong;
	}

	public String getName() {
		return name;
	}

	public String getId() {
		return id;
	}
	
}
