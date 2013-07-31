package info.kwarc.sally.core;

public class MessageForward {
	String type;
	Object data;
	
	public MessageForward(String type, Object data) {
		this.type = type;
		this.data = data;
	}
	
	public Object getData() {
		return data;
	}
	
	public String getType() {
		return type;
	}
}
