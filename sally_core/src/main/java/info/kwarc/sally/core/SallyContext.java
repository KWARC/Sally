package info.kwarc.sally.core;

public interface SallyContext {
	SallyInteraction getCurrentInteraction();
	Object getContextVar(String key);
	void setContextVar(String key, Object value);
	public <T> T getContextVar(String key, Class<T> cls);
	String getID();
}
