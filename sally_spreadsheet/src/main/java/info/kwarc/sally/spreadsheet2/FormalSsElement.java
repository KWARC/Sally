package info.kwarc.sally.spreadsheet2;

public class FormalSsElement {
	CellSpaceInformation position;
	String value, formula;
	ContentValueType valueType;
	
	public FormalSsElement(CellSpaceInformation position, String value, String formula, ContentValueType valueType) {
		super();
		this.position = position;
		this.value = value;
		this.formula = formula;
		this.valueType = valueType;
	}
		
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((formula == null) ? 0 : formula.hashCode());
		result = prime * result
				+ ((position == null) ? 0 : position.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		result = prime * result
				+ ((valueType == null) ? 0 : valueType.hashCode());
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
		FormalSsElement other = (FormalSsElement) obj;
		if (formula == null) {
			if (other.formula != null)
				return false;
		} else if (!formula.equals(other.formula))
			return false;
		if (position == null) {
			if (other.position != null)
				return false;
		} else if (!position.equals(other.position))
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		if (valueType != other.valueType)
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "Postion: " + position.toString() + " Value: " + value.toString() + " Type: " + valueType.toString();
	}

	public CellSpaceInformation getPosition() {
		return new CellSpaceInformation(position);
	}
	
	public void setPosition(CellSpaceInformation position) {
		this.position = position;
	}
	
	public String getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
	}
	
	public String getFormula() {
		return formula;
	}

	public void setFormula(String formula) {
		this.formula = formula;
	}

	public ContentValueType getValueType() {
		return valueType;
	}

	public void setValueType(ContentValueType valueType) {
		this.valueType = valueType;
	}

}
