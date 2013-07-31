package info.kwarc.sally.core.interfaces;

import java.util.Map;

public interface SallyAction {
	void run(Map<String, Object> parameters, SallyActionOutputAcceptor acceptor);
}
