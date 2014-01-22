package info.kwarc.sally.core.net;

import info.kwarc.sally.core.interaction.IMessageCallback;

import com.google.protobuf.AbstractMessage;

public interface INetworkSender {
	void sendMessage(String channel, AbstractMessage msg);
	void sendMessage(String channel, AbstractMessage msg, IMessageCallback callback);
}
