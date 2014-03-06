package info.kwarc.sally.networking;

import org.eclipse.jetty.server.Handler;

public interface IRequestHandler {
	public Handler onInit();
	public void onStart();
}
