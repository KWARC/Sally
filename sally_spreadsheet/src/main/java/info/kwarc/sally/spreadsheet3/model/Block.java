package info.kwarc.sally.spreadsheet3.model;

import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretation;

import java.util.ArrayList;
import java.util.List;

abstract public class Block {
	
	int id;
	String worksheet;
	List<ValueInterpretation> valueInterpretations;
	
	public Block(int id, String worksheet, List<ValueInterpretation> valueInterpretations) {
		this.id = id;
		this.worksheet = worksheet;
		this.valueInterpretations = new ArrayList<ValueInterpretation>(valueInterpretations);
	}
	
	public Block(int id, String worksheet) {
		this.id = id;
		this.worksheet = worksheet;
		this.valueInterpretations = new ArrayList<ValueInterpretation>();
	}
	
	public int getId() {
		return this.id;
	}
	
	public String getWorksheet() {
		return this.worksheet;
	}
	
	public CellSpaceInformation getCellForIndex(int x, int y) {
		CellSpaceInformation posAbsolut = new CellSpaceInformation(this.worksheet, this.getMinRow()+x, this.getMinColumn()+y);
		if (this.getCells().contains(posAbsolut))
			return posAbsolut;
		else
			return null;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + id;
		result = prime
				* result
				+ ((valueInterpretations == null) ? 0 : valueInterpretations
						.hashCode());
		result = prime * result
				+ ((worksheet == null) ? 0 : worksheet.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Block other = (Block) obj;
		if (id != other.id)
			return false;
		if (valueInterpretations == null) {
			if (other.valueInterpretations != null)
				return false;
		} else if (!valueInterpretations.equals(other.valueInterpretations))
			return false;
		if (worksheet == null) {
			if (other.worksheet != null)
				return false;
		} else if (!worksheet.equals(other.worksheet))
			return false;
		return true;
	}
	
	public void setValueInterpretations(List<ValueInterpretation> valueInterpretations) {
		this.valueInterpretations = new ArrayList<ValueInterpretation>(valueInterpretations);
	}
	
	public void setValueInterpretation(ValueInterpretation valueInterpretation) {
		this.valueInterpretations = new ArrayList<ValueInterpretation>();
		this.valueInterpretations.add(valueInterpretation);
	}
	
	public List<ValueInterpretation> getValueInterpretations() {
		return valueInterpretations;
	}
	
	public String getValueInterpretation(String value) {
		String valueInterpretation = "";
		
		for (ValueInterpretation vi : valueInterpretations) {
			String interpretation = vi.getValueInterpretation(value);
			if (!interpretation.isEmpty()) {
				if (valueInterpretation.isEmpty())
					valueInterpretation = interpretation;
				else
					throw new java.lang.IllegalStateException("Multiple Interpretations for value: " + value);
			}
		}

		return valueInterpretation;
	}

	abstract public List<CellSpaceInformation> getCells();
	
	abstract public List<Block> getSubBlocks();
	
	abstract public int getMinRow();
	
	abstract public int getMaxRow();
	
	abstract public int getMinColumn();
	
	abstract public int getMaxColumn();
	
	abstract public sally.BlockMsg serialize();
	
	public static Block createBlockFromMessage(sally.BlockMsg msg, Manager manager) {
		List<ValueInterpretation> vi = new ArrayList<ValueInterpretation>();
		for (sally.ValueInterpretationMsg viMsg : msg.getValueInterpretationsList())
			vi.add(new ValueInterpretation(viMsg));
		
		if (msg.getType().equals(sally.BlockMsg.Type.Atomic)) {
			return new BlockAtomic(msg.getId(), new CellSpaceInformation(msg.getPosition()), vi);
		} else if (msg.getType().equals(sally.BlockMsg.Type.Composed)) {
			List<Block> subBlocks = new ArrayList<Block>();
			for (int blockId : msg.getSubBlockIdsList())
				subBlocks.add(manager.getBlockByID(blockId));
			return new BlockComposed(msg.getId(), subBlocks, vi);
		} else
			throw new java.lang.IllegalArgumentException("Unknown blocktype.");
	}
	
}
