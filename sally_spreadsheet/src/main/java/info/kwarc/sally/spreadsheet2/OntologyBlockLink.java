package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

class OntologyBlockLink {
	
	String uri;
	List<ValueInterpretation> valueInterpretations;
	
	public OntologyBlockLink(String uri, List<ValueInterpretation> valueInterpretations) {
		super();
		this.uri = uri;
		this.valueInterpretations = valueInterpretations;
	}
	
	public OntologyBlockLink(String uri, ValueInterpretation valueInterpretation) {
		super();
		this.uri = uri;
		this.valueInterpretations = new ArrayList<ValueInterpretation>();
		this.valueInterpretations.add(valueInterpretation);
	}
	
	public String getUri() {
		return uri;
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
	
}
