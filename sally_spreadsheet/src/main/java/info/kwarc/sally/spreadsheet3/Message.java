package info.kwarc.sally.spreadsheet3;

import java.util.ArrayList;
import java.util.List;

/**
 * Some methods return a list of messages to provide feedback.
 * @author cliguda
 *
 */
public class Message {
	
	/**
	 * The message type indicates whether the message is related to blocks, relation or the semantic model. 
	 * @author cliguda
	 *
	 */
	public enum MessageType {
		BlockMsg, RelationMsg, SemanticModelMsg 
	}
	
	/**
	 * The message subtype specifies the type of information.
	 * @author cliguda
	 *
	 */
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
