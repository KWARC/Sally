package info.kwarc.sally.networking.interfaces;

import com.google.protobuf.AbstractMessage;

/**
 * This interface is the main gateway for passing messages from 
 * networking frameworks to/from Sally. 
 * @author Constantin Jucovschi
 */

public interface IConnectionManager {

	/**
	 * A new client identified by clientID connected to sally
	 * @param clientID
	 */
	public abstract void newClient(String clientID, INetworkSender sender);

	/**
	 * This method is there mostly for Workflow debugging purposes. It allows 
	 * testing workflows without sending real messages.
	 * @param clientID - identifier of the client that sent the message
	 * @param type - the type of message 
	 * @param data - message object to be passed to the workflows
	 */
	public abstract void newMessage(String clientID, String type, Object data);

	/**
	 * This method notifies Sally there a message was received from the client.
	 * @param clientID - identifies the client that send the message
	 * @param msg - ProtoBuffer message
	 */
	public abstract void newMessage(String clientID, AbstractMessage msg);

	public abstract void onSendMessage(String clientID, String channel, AbstractMessage msg);
	
	/**
	 * This method notifies Sally that a client disconnected.
	 * @param clientID - identifies the client that disconnected
	 */
	public abstract void disconnect(String clientID);
}