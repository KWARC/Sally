package info.kwarc.sally.core;

import java.util.Map;

public interface SallyAction {
	void run(Map<String, Object> parameters);
}
