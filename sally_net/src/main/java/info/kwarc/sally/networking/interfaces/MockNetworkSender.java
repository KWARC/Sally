package info.kwarc.sally.networking.interfaces;

import com.google.protobuf.AbstractMessage;

public class MockNetworkSender implements INetworkSender {

	@Override
	public void sendMessage(String channel, AbstractMessage msg) {
	}

	@Override
	public void sendMessage(String channel, AbstractMessage msg,
			IMessageCallback callback) {
	}

}
