package info.kwarc.sally.networking.cometd;

import info.kwarc.sally.core.SallyInteraction;

import org.cometd.bayeux.server.ServerChannel;
import org.cometd.server.BayeuxServerImpl;
import org.cometd.server.CometdServlet;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;

public class CometD {
	int port;
	Server server;
	CometdServlet cometdServlet;

	public CometD(int port) {
		this.port = port;
	}
	
	BayeuxServerImpl getBayeux() {
		return cometdServlet.getBayeux();
	}
	
	public void channelToInteraction(SallyInteraction interaction) {
//		BayeuxServerImpl _bayeux = getBayeux();
//		_bayeux.createIfAbsent(channelName);
		
	}
	
	public void registerListener(String channelName, ServerChannel.MessageListener listener) {
		BayeuxServerImpl _bayeux = getBayeux();
		_bayeux.createIfAbsent(channelName);
		
        _bayeux.getChannel(channelName).addListener(listener);
	}
	
	public void start() {
		server = new Server(8080);
		cometdServlet = new CometdServlet();
		ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
		context.setContextPath("/");
		server.setHandler(context);

		context.addServlet(new ServletHolder(cometdServlet),"/sally/cometd/*");
		
		new Thread(new CometDThread()).start();
		while (cometdServlet.getBayeux() == null) {
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
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
