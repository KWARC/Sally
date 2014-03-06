package info.kwarc.sally.networking;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.eclipse.jetty.server.Handler;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.HandlerList;
import org.eclipse.jetty.server.handler.ResourceHandler;
import org.eclipse.jetty.util.resource.Resource;

import com.google.inject.Inject;
import com.google.inject.name.Named;

public class SallyServer {
	Server server;
	int port;
	Set<IRequestHandler> requesthandlers;
	
	@Inject
	public SallyServer(@Named("SallyPort") int port, 	Set<IRequestHandler> requesthandlers) {
		this.port = port;
		this.requesthandlers = requesthandlers;
	}
	
	public void start() {
		server = new Server(port);
		// Defines a list of handlers that will be processed in order in order to answer requests
		HandlerList handlers = new HandlerList();

		// ResourceHandler will serve static files 
		ResourceHandler resource_handler = new ResourceHandler();
		resource_handler.setDirectoriesListed(true);
		resource_handler.setWelcomeFiles(new String[] { "index.html" });
		resource_handler.setBaseResource(Resource.newClassPathResource("sally/web"));

		List<Handler> hndList = new ArrayList<Handler>();
		hndList.add(resource_handler);
		for (IRequestHandler handler : requesthandlers) {
			Handler hnd = handler.onInit();
			if (hnd != null)
				hndList.add(hnd);
		}
		
		handlers.setHandlers(hndList.toArray(new Handler[0]));
		server.setHandler(handlers);

		new Thread(new CometDThread()).start();
	}
	
	private class CometDThread implements Runnable {

		public void run() {
			try {
				server.start();
				server.join();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}
}
