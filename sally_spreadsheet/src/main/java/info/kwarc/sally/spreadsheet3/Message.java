package info.kwarc.sally.spreadsheet3;

import java.util.ArrayList;
import java.util.List;

public class Message {
	
	public enum MessageType {
		BlockMsg, RelationMsg, SemanticModelMsg 
	}
	
	public enum MessageSubType {
		Info, Error, Succeed, SemanticIncomplete
	}
	
	MessageType type;
	MessageSubType subType;
	String message;
	List<Integer> ids;
	
	public Message(MessageType type, MessageSubType subType, String message,
			List<Integer> ids) {
		super();
		this.type = type;
		this.subType = subType;
		this.message = message;
		this.ids = ids;
	}
	
	public Message(MessageType type, MessageSubType subType, String message) {
		this(type, subType, message, new ArrayList<Integer>());
	}
	
	public Message(MessageType type, MessageSubType subType, String message, int id) {
		this(type, subType, message, new ArrayList<Integer>());
		this.ids.add(id);
	}

	public MessageType getType() {
		return type;
	}

	public MessageSubType getSubType() {
		return subType;
	}

	public String getMessage() {
		return message;
	}

	public List<Integer> getIds() {
		return ids;
	}
}
