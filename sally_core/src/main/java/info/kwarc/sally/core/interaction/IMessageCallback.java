package info.kwarc.sally.core.interaction;

import com.google.protobuf.AbstractMessage;

public interface IMessageCallback {
	void onMessage(AbstractMessage msg);
}
