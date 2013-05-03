package info.kwarc.sally.model.document.spreadsheet;

import java.util.List;

public class FormalSsElement {
	int id;				// Just for management reasons
	String value;
	ContentValueType valueType;
	List<CellSpaceInformation> parameters;
	//TODO: formulae is missing
	
	public FormalSsElement(int id, String value, ContentValueType valueType,
			List<CellSpaceInformation> parameters) {
		super();
		this.value = value;
		this.valueType = valueType;
		this.parameters = parameters;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + id;
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
		if (id != other.id)
			return false;
		return true;
	}
	
	public boolean isEquivalent(FormalSsElement e) {
		if (this == e)
			return true;
		if (e == null)
			return false;
		return (this.value.equals(e.getValue()) && this.valueType.equals(e.getValueType()) && this.parameters.equals(e.getParameters()));
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

	public List<CellSpaceInformation> getParameters() {
		return parameters;
	}

	public void setParameters(List<CellSpaceInformation> parameters) {
		this.parameters = parameters;
	}
}
