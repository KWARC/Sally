package info.kwarc.sally.core;

import java.util.HashMap;

public class SallyContextImpl implements SallyContext {
	SallyInteraction interaction;
	HashMap<String, Object> vars;
	
	public SallyContextImpl() {
		vars = new HashMap<String, Object>();
	}
	
	public void setInteraction(SallyInteraction interaction) {
		this.interaction = interaction;
	}
	
	public SallyInteraction getCurrentInteraction() {
		return interaction;
	}
	
	public Object getContextVar(String key) {
		return vars.get(key);
	}
	
	public void setContextVar(String key, Object value){
		vars.put(key, value);
	}
}
