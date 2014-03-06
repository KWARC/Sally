package info.kwarc.sally.core.workflow;

import java.util.Collection;
import java.util.Map;

import com.google.protobuf.AbstractMessage;

public interface ProcessInstance {
	Map<String, Object> getProcessVariables();
	void setProcessVarialbe(String var, Object value);

	void sendMessageOrForward(Long from, String type, Object data);
	void sendMessageOrForward(Long from, AbstractMessage data);

	void signalEvent(String msg, Object data);
	
	public Collection<String> getCallableEvents();
	
	Long getId();
	
}
