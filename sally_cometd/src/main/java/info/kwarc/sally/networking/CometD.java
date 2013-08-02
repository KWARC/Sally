package info.kwarc.sally.networking;

import info.kwarc.sally.networking.interfaces.IConnectionManager;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Map;

import org.cometd.bayeux.Channel;
import org.cometd.bayeux.server.BayeuxServer;
import org.cometd.bayeux.server.ServerChannel;
import org.cometd.bayeux.server.ServerSession;
import org.cometd.server.BayeuxServerImpl;
import org.cometd.server.CometdServlet;
import org.eclipse.jetty.server.Handler;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.DefaultHandler;
import org.eclipse.jetty.server.handler.HandlerList;
import org.eclipse.jetty.server.handler.ResourceHandler;
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
import com.google.protobuf.AbstractMessage;
import com.sun.jersey.api.core.PackagesResourceConfig;
import com.sun.jersey.spi.container.servlet.ServletContainer;

import freemarker.template.Configuration;
import freemarker.template.Template;
import freemarker.template.TemplateException;

public class CometD {
	int port;
	Server server;
	CometdServlet cometdServlet;
	Configuration cfg;
	IConnectionManager connManager;

	Logger log;

	@Inject
	public CometD(int port, IConnectionManager connManager) {
		this.port = port;
		log = LoggerFactory.getLogger(CometD.class);
		this.connManager = connManager;
	}

	BayeuxServerImpl getBayeux() {
		return cometdServlet.getBayeux();
	}

	public void sendMsg(CometDSendRequest request) {
		log.debug(String.format("<-- [%s]: %s", request.getChannel(), request.getMsg().getClass().getName()));

		ServerSession sess = getBayeux().getSession(request.getClientID());
		sess.deliver(sess, request.getChannel(), ProtoUtils.prepareProto(request.getMsg()), null);
	}

	public String generateTemplate(String templatePath, Object data) {
		StringWriter w = new StringWriter();
		Template tpl;
		try {
			tpl = cfg.getTemplate(templatePath);
			tpl.process(data, w);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (TemplateException e) {
			e.printStackTrace();
		}
		return w.toString();
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
		HandlerList handlers = new HandlerList();

		ResourceHandler resource_handler = new ResourceHandler();
		resource_handler.setDirectoriesListed(true);
		resource_handler.setWelcomeFiles(new String[] { "index.html" });
		resource_handler.setBaseResource(Resource.newClassPathResource("sally/web"));

		cometdServlet = new CometdServlet();
		ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
		context.setContextPath("/");

		handlers.setHandlers(new Handler[] { resource_handler, context, new DefaultHandler() });

		server.setHandler(handlers);

		context.addServlet(new ServletHolder(new ServletContainer(new PackagesResourceConfig("info.kwarc.sally"))), "/*");
		context.addServlet(new ServletHolder(cometdServlet),"/sally/cometd/*");

		cfg = new Configuration();
		cfg.setClassForTemplateLoading(getClass(), "/sally");

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
