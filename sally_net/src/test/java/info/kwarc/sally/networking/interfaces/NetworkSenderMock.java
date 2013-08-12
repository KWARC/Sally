package info.kwarc.sally.networking.interfaces;

import com.google.protobuf.AbstractMessage;

public class NetworkSenderMock implements INetworkSender {

	@Override
	public void sendMessage(String channel, AbstractMessage msg) {
		return;
	}

	@Override
	public void sendMessage(String channel, AbstractMessage msg,
			IMessageCallback callback) {
		return;		
	}

}
