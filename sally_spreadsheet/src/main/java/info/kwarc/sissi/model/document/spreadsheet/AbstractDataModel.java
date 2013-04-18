package info.kwarc.sissi.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;


public class AbstractDataModel {
	
	List<AbstractSsElement> elements; 
	int id = 0;
	
	public AbstractDataModel() {
		elements = new ArrayList<AbstractSsElement>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((elements == null) ? 0 : elements.hashCode());
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
		AbstractDataModel other = (AbstractDataModel) obj;
		if (elements == null) {
			if (other.elements != null)
				return false;
		} else if (!elements.equals(other.elements))
			return false;
		if (id != other.id)
			return false;
		return true;
	}

	public AbstractSsElement createElement(String value, ContentValueType valueType,
			List<AbstractSsElement> parameters) {
		AbstractSsElement e = new AbstractSsElement(id, value, valueType, parameters);
		elements.add(e);
		id++;
		return e;
	}
	
	// Constructor for reconstruction elements
	public AbstractSsElement createElement(int elementId, String value, ContentValueType valueType) {
		AbstractSsElement e = new AbstractSsElement(elementId, value, valueType, new ArrayList<AbstractSsElement>());
		elements.add(e);
		if (id == elementId)
			id++;
		else
			id = java.lang.Math.max(id, elementId+1);
		return e;
	}
	
	public List<AbstractSsElement> createElements(List<String> values, List<ContentValueType> valueTypes,
			List<List<AbstractSsElement>> parameters) {
		if ((values.size() != valueTypes.size()) || (valueTypes.size() != parameters.size())  )
			throw new java.lang.IllegalArgumentException("values, valueTypes and parameters have not the same size !");
		
		List<AbstractSsElement> created = new ArrayList<AbstractSsElement>();
		for (int i = 0; i < values.size(); i++)
			created.add(createElement(values.get(i), valueTypes.get(i), parameters.get(i)));
		return created;
	}
	
	public List<AbstractSsElement> getElementsByName(String name) {
		List<AbstractSsElement> foundElements = new ArrayList<AbstractSsElement>();
		for (AbstractSsElement e : elements)
			if (e.getValue().equals(name))
				foundElements.add(e);
		return foundElements;
	}
	
	public AbstractSsElement getElementById(int id) {
		for (AbstractSsElement e : elements)
			if (e.getId() == id)
				return e;
		return null;
	}
	
	public void removeElement(AbstractSsElement e) {
		elements.remove(e);
	}
	
	public sally.AbstractDataModelMsg getProtoBufRepresentation() {
		sally.AbstractDataModelMsg.Builder msgBuilder = sally.AbstractDataModelMsg.newBuilder();
		for (AbstractSsElement e : elements)
			msgBuilder.addElements( e.getProtoBufRepresentation());
		return msgBuilder.build();
	}
	
	public void print() {
		System.out.println("Printing data from model");
		System.out.println("MaxId: " + id);
		for (AbstractSsElement e : elements)
			e.print();
	}
	

}
