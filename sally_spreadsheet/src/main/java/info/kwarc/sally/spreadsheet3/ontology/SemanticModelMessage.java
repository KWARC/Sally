package info.kwarc.sally.spreadsheet3.ontology;

import java.util.ArrayList;
import java.util.List;

public class SemanticModelMessage {
	
	enum MessageType {
		VALID, ERROR, UNCHECKED, INCOMPLETEBLOCK
	}
	
	MessageType type;
	List<Integer> idList;
	
	public SemanticModelMessage(MessageType type, List<Integer> idList) {
		this.type = type;
		if (idList != null)
			this.idList = idList;
		else
			this.idList = new ArrayList<Integer>();
	}
	
	public SemanticModelMessage(MessageType type, int id) {
		this(type, null);
		idList.add(id);
	}
	
	public SemanticModelMessage(MessageType type) {
		this(type, null);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((idList == null) ? 0 : idList.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		SemanticModelMessage other = (SemanticModelMessage) obj;
		if (idList == null) {
			if (other.idList != null)
				return false;
		} else if (!idList.equals(other.idList))
			return false;
		if (type != other.type)
			return false;
		return true;
	}

	public String getMessage() {
		String message;
		switch (type) {
		case VALID:
			message = "Everything is valid.";
			break;
		case ERROR:
			message = "Something went wrong.";
			break;
		case UNCHECKED:
			message = "Nothing found to be validated.";
			break;
		case INCOMPLETEBLOCK:
			message = "One or more blocks are no semantic complete representations of an ontology concept.";
			break;
		default:
			message = "Unknown message type: " + type.name();
		}
		return message;
	}

	public MessageType getType() {
		return type;
	}

	public List<Integer> getIdList() {
		return idList;
	}
	
}
