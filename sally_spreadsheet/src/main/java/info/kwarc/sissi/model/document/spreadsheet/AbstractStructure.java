package info.kwarc.sissi.model.document.spreadsheet;

public abstract class AbstractStructure {
	private int id;

	public AbstractStructure(int id) {
		super();
		this.id = id;
	}

	public int getId() {
		return id;
	}

}
