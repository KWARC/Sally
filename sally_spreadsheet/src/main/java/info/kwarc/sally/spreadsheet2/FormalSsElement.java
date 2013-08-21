package info.kwarc.sally.spreadsheet2;

class FormalSsElement {
	CellSpaceInformation position;
	String value;
	ContentValueType valueType;
	//TODO: formulae is missing
	
	public FormalSsElement(CellSpaceInformation position, String value, ContentValueType valueType) {
		super();
		this.position = position;
		this.value = value;
		this.valueType = valueType;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
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

	public ContentValueType getValueType() {
		return valueType;
	}

	public void setValueType(ContentValueType valueType) {
		this.valueType = valueType;
	}

}
