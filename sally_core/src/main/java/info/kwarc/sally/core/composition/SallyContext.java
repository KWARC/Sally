package info.kwarc.sally.core.composition;

public interface SallyContext {
	SallyInteraction getCurrentInteraction();
	Object getContextVar(String key);
	void setContextVar(String key, Object value);
	<T> T getContextVar(String key, Class<T> cls);
	String getID();
	SallyContext createClone();
}
