package info.kwarc.sally.networking;

import com.google.protobuf.AbstractMessage;

public class CometDSendRequest {
	String channel;
	AbstractMessage msg;
	String clientID;
	
	public CometDSendRequest(String clientID, String channel, AbstractMessage msg) {
		this.channel = channel;
		this.msg = msg;
		this.clientID = clientID;
	}
	
	public String getChannel() {
		return channel;
	}
	
	public String getClientID() {
		return clientID;
	}
	
	public AbstractMessage getMsg() {
		return msg;
	}
	
}
