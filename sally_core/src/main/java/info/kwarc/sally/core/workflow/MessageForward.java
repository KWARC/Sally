package info.kwarc.sally.core.workflow;

/**
 * 
 * @author Constantin Jucovschi
 * 
 * MessageForward encapsules a request that could not be matched to any event in the current event gateway. 
 *
 */
public class MessageForward {
	String type;
	Long from;
	Object data;
	
	public MessageForward(Long from, String type, Object data) {
		this.type = type;
		this.data = data;
		this.from = from;
	}
	
	public Object getData() {
		return data;
	}
	
	public String getType() {
		return type;
	}
	
	public Long getFrom() {
		return from;
	}
}
