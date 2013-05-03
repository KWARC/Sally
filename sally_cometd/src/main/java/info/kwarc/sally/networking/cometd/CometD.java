package info.kwarc.sally.networking.cometd;

import info.kwarc.sally.core.SallyInteraction;

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

import com.github.jucovschi.ProtoCometD.CommunicationCallback;
import com.github.jucovschi.ProtoCometD.CommunicationContext;
import com.github.jucovschi.ProtoCometD.ProtoService;
import com.google.protobuf.AbstractMessage;
import com.sun.jersey.api.core.PackagesResourceConfig;
import com.sun.jersey.spi.container.servlet.ServletContainer;

import freemarker.template.Configuration;

public class CometD {
	int port;
	Server server;
	CometdServlet cometdServlet;
	private static Configuration cfg;
	
	public static Configuration getTemplatingEngine() {
		return cfg;
	}
	
	public CometD(int port) {
		this.port = port;
	}
	
	BayeuxServerImpl getBayeux() {
		return cometdServlet.getBayeux();
	}

	class CometDProtoService extends ProtoService {
		SallyInteraction interaction;

		public CometDProtoService(BayeuxServer bayeux, String name, SallyInteraction interaction) {
			super(bayeux, name);
			this.interaction = interaction;
			addService("/service/**", CommunicationCallback.newBuilder().allowMessages(AbstractMessage.class).build("forward", this));
		}

		public AbstractMessage forward(ServerSession remote, final AbstractMessage msg, CommunicationContext context) {
			System.out.println("sending to "+context.getChannel()+" "+msg.getClass());
			return interaction.getOneInteraction(context.getChannel(), msg, AbstractMessage.class);
		}
	}

	public void channelToInteraction(final SallyInteraction interaction) {
		new CometDProtoService(getBayeux(), "fowarder", interaction);
	}

	public void registerListener(String channelName, ServerChannel.MessageListener listener) {
		BayeuxServerImpl _bayeux = getBayeux();
		_bayeux.createIfAbsent(channelName);

		_bayeux.getChannel(channelName).addListener(listener);
	}

	public void start() {
		server = new Server(8080);
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
/*		
		cfg.setDirectoryForTemplateLoading(
				new File("/where/you/store/templates"));
		cfg.setObjectWrapper(new DefaultObjectWrapper());
*/

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
