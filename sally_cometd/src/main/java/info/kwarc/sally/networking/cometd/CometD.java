package info.kwarc.sally.networking.cometd;

import java.io.IOException;
import java.io.StringWriter;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

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

	private static SallyInteraction interaction;
	Logger log;
		
	public static SallyInteraction getInteraction() {
		return interaction;
	}
	
	public CometD(int port) {
		this.port = port;
		log = LoggerFactory.getLogger(CometD.class);
	}
	
	BayeuxServerImpl getBayeux() {
		return cometdServlet.getBayeux();
	}
	
	@SallyService
	public void sendMsg(CometDSendRequest request, SallyActionAcceptor acceptor, SallyContext context) {
		log.debug(String.format("<-- [%s]: %s", request.getChannel(), request.getMsg().getClass().getName()));
		
		ServerSession sess = getBayeux().getSession(request.getClientID());
		sess.deliver(sess, request.getChannel(), ProtoUtils.prepareProto(request.getMsg()), null);
	}
	
	@SallyService(channel="/template/generate")
	public void generateTemplate(TemplateRequest request, SallyActionAcceptor acceptor, SallyContext context) {
		try {
			StringWriter w = new StringWriter();
			Template tpl = cfg.getTemplate(request.getTemplatePath());
			tpl.process(request.getData(), w);
			acceptor.acceptResult(w.toString());
		} catch (IOException e) {
			e.printStackTrace();
		} catch (TemplateException e) {
			e.printStackTrace();
		}
	}
	
	class CometDProtoService extends ProtoService {
		SallyInteraction interaction;

		public CometDProtoService(BayeuxServer bayeux, String name, SallyInteraction interaction) {
			super(bayeux, name);
			this.interaction = interaction;
			addService("/service/**", CommunicationCallback.newBuilder().allowMessages(AbstractMessage.class).build("forward", this));
		}

		public AbstractMessage forward(ServerSession remote, final AbstractMessage msg, CommunicationContext context) {
			log.debug(String.format("--> [%s]: %s", context.getChannel(), msg.getClass().getName()));
			SallyContext interactionContext = interaction.getContext();
			interactionContext.setContextVar("senderID", remote.getId());
			return interaction.getOneInteraction(context.getChannel(), msg, AbstractMessage.class);
		}
	}

	public void channelToInteraction(final SallyInteraction interaction) {
		CometD.interaction = interaction;
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
