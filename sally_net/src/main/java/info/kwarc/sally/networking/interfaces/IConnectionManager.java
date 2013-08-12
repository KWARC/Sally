package info.kwarc.sally.networking.interfaces;

import com.google.protobuf.AbstractMessage;

public interface IConnectionManager {

	public abstract void newClient(String clientID);

	public abstract void newMessage(String clientID, String type, Object data);

	public abstract void newMessage(String clientID, AbstractMessage msg);

	public abstract void disconnect(String clientID);
	
}