package info.kwarc.sally.core;

import java.util.HashMap;

public class SallyContextImpl implements SallyContext {
	SallyInteraction interaction;
	HashMap<String, Object> vars;
	String token;

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

	@Override
	public String getID() {
		return token;
	}

	public void setToken(String token) {
		this.token = token;
	}

	@Override
	public <T> T getContextVar(String key, Class<T> cls) {
		if (!vars.containsKey(key))
			return null;
		Object result = vars.get(key);
		if (cls.isInstance(result))
			return (cls.cast(result));
		return null;
	}

}
