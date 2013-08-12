package info.kwarc.sally.networking;

import com.google.protobuf.AbstractMessage;

public class CometDSendRequest {
	String channel;
	AbstractMessage msg;
	
	public CometDSendRequest(String channel, AbstractMessage msg) {
		this.channel = channel;
		this.msg = msg;
	}
	
	public String getChannel() {
		return channel;
	}
		
	public AbstractMessage getMsg() {
		return msg;
	}
	
}
