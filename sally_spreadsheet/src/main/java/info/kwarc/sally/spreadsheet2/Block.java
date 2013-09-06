package info.kwarc.sally.spreadsheet2;

import java.util.List;

abstract public class Block {
	
	int id;
	OntologyBlockLink ontologyLink;
	
	public Block(int id) {
		this.id = id;
		this.ontologyLink = null;
	}
	
	public Block(int id, OntologyBlockLink ontologyLink) {
		this.id = id;
		this.ontologyLink = ontologyLink;
	}
	
	abstract public int hashCode();
	
	abstract public boolean equals(Object obj);
	
	abstract public List<CellSpaceInformation> getCells();
	
	abstract public List<Block> getSubBlocks();
	
	public int getId() {
		return this.id;
	}

	public OntologyBlockLink getOntologyLink() {
		return ontologyLink;
	}

	public void setOntologyLink(OntologyBlockLink ontologyLink) {
		this.ontologyLink = ontologyLink;
	}
	
}
