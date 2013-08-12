package info.kwarc.sally.model.ontology2.ValueInterpreters;

import info.kwarc.sally.model.ontology2.ValueInterpretation;

public class StringValue implements ValueInterpretation {
	
	@Override
	public String interpret(String key) {
		key = key.replace(' ', '-');
		return key;
	}

}
