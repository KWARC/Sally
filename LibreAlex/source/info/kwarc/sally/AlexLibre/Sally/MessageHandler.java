package info.kwarc.sally.AlexLibre.Sally;

import org.cometd.bayeux.client.ClientSessionChannel;

import com.google.protobuf.AbstractMessage;

public interface MessageHandler {
	Object onMessage(ClientSessionChannel session, String channel, AbstractMessage msg);
}
