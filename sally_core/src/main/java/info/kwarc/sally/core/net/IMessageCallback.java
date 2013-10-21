package info.kwarc.sally.core.net;

import com.google.protobuf.AbstractMessage;

public interface IMessageCallback {
	void onMessage(AbstractMessage msg);
}
