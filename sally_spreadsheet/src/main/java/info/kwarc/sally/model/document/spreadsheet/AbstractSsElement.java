package info.kwarc.sally.model.document.spreadsheet;

import java.util.List;


public class AbstractSsElement {
	int id;				// Just for management reasons
	String value;
	ContentValueType valueType;
	String formula = "";	//TODO: formulae is missing
	List<AbstractSsElement> parameters;
	
	public AbstractSsElement(int id, String value, ContentValueType valueType,
			List<AbstractSsElement> parameters) {
		super();
		this.id = id;
		this.value = value;
		this.valueType = valueType;
		this.parameters = parameters;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((formula == null) ? 0 : formula.hashCode());
		result = prime * result + id;
		result = prime * result
				+ ((parameters == null) ? 0 : parameters.hashCode());
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
		AbstractSsElement other = (AbstractSsElement) obj;
		if (formula == null) {
			if (other.formula != null)
				return false;
		} else if (!formula.equals(other.formula))
			return false;
		if (id != other.id)
			return false;
		if (parameters == null) {
			if (other.parameters != null)
				return false;
		} else if (!parameters.equals(other.parameters))
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

	public int getId() {
		return id;
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

	public List<AbstractSsElement> getParameters() {
		return parameters;
	}

	public void setParameters(List<AbstractSsElement> parameters) {
		this.parameters = parameters;
	}
	
	public sally.AbstractElementMsg getProtoBufRepresentation() {
		sally.AbstractElementMsg.Builder msgBuilder = sally.AbstractElementMsg.newBuilder().setId(id).setValue(value);
		for (int i = 0; i < parameters.size(); i++)
			msgBuilder.setParameters(i, parameters.get(i).getId()); 
		return msgBuilder.build();
	}
	
	public void print() {
		System.out.print("Id: " + id + " value: " + value + " (" + valueType + ")" + " Formula: " + formula + " Paramters: ");
		for (AbstractSsElement p : parameters)
			System.out.print(p.getId() + " ");
		System.out.println();
	}
	
}