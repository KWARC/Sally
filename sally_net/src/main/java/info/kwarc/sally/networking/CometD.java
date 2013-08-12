package info.kwarc.sally.networking;

import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.networking.interfaces.IMessageCallback;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.networking.interfaces.INetworkSenderAdapter;

import java.util.EnumSet;
import java.util.Map;

import org.cometd.bayeux.Channel;
import org.cometd.bayeux.server.BayeuxServer;
import org.cometd.bayeux.server.LocalSession;
import org.cometd.bayeux.server.ServerChannel;
import org.cometd.bayeux.server.ServerSession;
import org.cometd.server.BayeuxServerImpl;
import org.cometd.server.CometdServlet;
import org.eclipse.jetty.server.DispatcherType;
import org.eclipse.jetty.server.Handler;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.HandlerList;
import org.eclipse.jetty.server.handler.ResourceHandler;
import org.eclipse.jetty.servlet.DefaultServlet;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;
import org.eclipse.jetty.util.resource.Resource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.github.jucovschi.ProtoCometD.CommunicationCallback;
import com.github.jucovschi.ProtoCometD.CommunicationContext;
import com.github.jucovschi.ProtoCometD.ProtoService;
import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.Singleton;
import com.google.inject.name.Named;
import com.google.inject.servlet.GuiceFilter;
import com.google.protobuf.AbstractMessage;

@Singleton
public class CometD implements Provider<INetworkSenderAdapter> {
	int port;
	Server server;
	CometdServlet cometdServlet;
	IConnectionManager connManager;
	LocalSession localSession;
	
	INetworkSenderAdapter adapter = new INetworkSenderAdapter() {		
		@Override
		public INetworkSender create(final String clientID) {
			return new INetworkSender() {
				
				@Override
				public void sendMessage(String channel, AbstractMessage msg,
						IMessageCallback callback) {
					_sendMessage(clientID, channel, msg, callback);
				}
				
				@Override
				public void sendMessage(String channel, AbstractMessage msg) {
					_sendMessage(clientID, channel, msg);
				}
			};
		}
	};
	
	Logger log;
	
	@Inject
	public CometD(@Named("SallyPort") int port, IConnectionManager connManager) {
		this.port = port;
		log = LoggerFactory.getLogger(CometD.class);
		this.connManager = connManager;
		log.error("new CometD instance");
	}
	
	BayeuxServerImpl getBayeux() {
		return cometdServlet.getBayeux();
	}

	class CometDProtoService extends ProtoService {
		IConnectionManager connManager;
		
		public CometDProtoService(BayeuxServer bayeux, String name, IConnectionManager connManager) {
			super(bayeux, name);
			this.connManager = connManager;
			
			addService("/service/**", CommunicationCallback.newBuilder().allowMessages(AbstractMessage.class).build("forward", this));
			
			addService(Channel.META_CONNECT, "onConnect");
			addService(Channel.META_DISCONNECT, "onDisconnect");

		}

		public AbstractMessage forward(ServerSession remote, final AbstractMessage msg, CommunicationContext context) {
			log.info(remote.getId()+" got message "+msg);
			log.debug(String.format("--> [%s]: %s", context.getChannel(), msg.getClass().getName()));
			connManager.newMessage(remote.getId(), msg);
			return null;
		}
		
		public void onConnect(ServerSession remote, Map<String, Object> data) {
			log.info(remote.getId()+" connected");
			this.connManager.newClient(remote.getId());
		}
		
		public void onDisconnect(ServerSession remote, Map<String, Object> data) {
			log.info(remote.getId()+" disconnected");
			this.connManager.disconnect(remote.getId());
		}
	}

	public void registerListener(String channelName, ServerChannel.MessageListener listener) {
		BayeuxServerImpl _bayeux = getBayeux();
		_bayeux.createIfAbsent(channelName);

		_bayeux.getChannel(channelName).addListener(listener);
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

		// context will contain the rest of the servlets  
		ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
		context.setContextPath("/");

		// setting everything up
		handlers.setHandlers(new Handler[] { resource_handler, context});
		server.setHandler(handlers);

		cometdServlet = new CometdServlet();
		
		context.addServlet(new ServletHolder(cometdServlet),"/cometd/*");
		context.addFilter(GuiceFilter.class, "/sally/*", EnumSet.allOf(DispatcherType.class));
		context.addServlet(new ServletHolder(new DefaultServlet()), "/*");
		
		new Thread(new CometDThread()).start();
		while (cometdServlet.getBayeux() == null) {
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		new CometDProtoService(getBayeux(), "", connManager);
		localSession = getBayeux().newLocalSession("Sally");
		localSession.handshake();
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

	private void _sendMessage(String clientID, String channel, AbstractMessage msg) {
		Map<String, Object> data = ProtoUtils.prepareProto(msg);		
		ServerSession sess = getBayeux().getSession(clientID);
		if (sess == null) {
			log.error(("Session "+clientID+" does not exist"));
			return;
		}
		sess.deliver(localSession, channel, data, "6");
	}
	
	private void _sendMessage(String clientID, String channel, AbstractMessage msg, IMessageCallback callback) {
		Map<String, Object> data = ProtoUtils.prepareProto(msg);		
		ServerSession sess = getBayeux().getSession(clientID);
		if (sess == null) {
			log.error(("Session "+clientID+" does not exist"));
			return;
		}
		
		sess.deliver(sess, channel, data, "asd");
	}

	@Override
	public INetworkSenderAdapter get() {
		return adapter;
	}
}
