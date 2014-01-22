package info.kwarc.sally.AlexLibre.Sally;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.cometd.bayeux.Channel;
import org.cometd.bayeux.Message;
import org.cometd.bayeux.client.ClientSessionChannel;
import org.cometd.client.BayeuxClient;
import org.cometd.client.transport.ClientTransport;
import org.cometd.client.transport.LongPollingTransport;
import org.eclipse.jetty.client.HttpClient;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.DocType;
import sally.WhoAmI;
import sally.WhoAmI.ClientType;
import sally.WhoAmI.EnvironmentType;

import com.google.protobuf.AbstractMessage;

public class SallyCommunication {

	Logger log;
	String host;
	int port;
	BayeuxClient client;
	List<MessageHandler> msgHanders;

	public SallyCommunication(String host, int port) {
		log = LoggerFactory.getLogger(getClass());
		this.host = host;
		this.port = port;
		msgHanders = new ArrayList<MessageHandler>();
		log.info("Sally Comm initialized");
	}

	public void addHandler(MessageHandler handler) {
		msgHanders.add(handler);
	}

	public class MessageParser implements ClientSessionChannel.MessageListener {
		Logger log;

		public MessageParser() {
			log = LoggerFactory.getLogger(getClass());
		}

		@Override
		public void onMessage(ClientSessionChannel session, Message message) {
			if (message.getData() == null)
				return;
			AbstractMessage msg;
			try {
				msg = Util.restoreMessage(message.getDataAsMap());
			} catch (Exception e) {
				e.printStackTrace();
				log.error(e.getMessage());
				return;
			}
			log.info(message.getChannel()+" "+msg);
			for (MessageHandler handler : msgHanders) {
				Object response = handler.onMessage(session, message.getChannel(), msg);
				if (response == null) 
					continue;
				if (response instanceof Boolean && ((Boolean) response))
					break;
				if (!(response instanceof AbstractMessage))
					continue;

				Map<String, Object> json = Util.prepareMessage((AbstractMessage)response);
				if (message.containsKey("msgid")) {
					json.put("rmsgid", message.get("msgid").toString());
				}
				session.publish(json);
			}

		}
	}

	public static class MessageLogger implements
	ClientSessionChannel.MessageListener {
		public MessageLogger() {
		}

		@Override
		public void onMessage(ClientSessionChannel session, Message message) {
			if (message.isSuccessful()) {
				// AbstractMessage msg = Util.restoreMessage(message);
				System.out.println("had something on " + message.getChannel());
				System.out.println("namely " + message.getJSON());

			}
		}
	}

	public int sendMessage(String channel, AbstractMessage msg) {
		client.getChannel(channel).publish(Util.prepareMessage(msg));
		return 0;
	}

	public void start() {
		HttpClient httpClient = new HttpClient();
		try {
			httpClient.start();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		try {
			// Prepare the transport
			Map<String, Object> options = new HashMap<String, Object>();
			ClientTransport transport = LongPollingTransport.create(options,
					httpClient);
			log.info("Connecting to " + this.host + ":" + this.port
					+ "/cometd");
			client = new BayeuxClient(this.host + ":" + this.port
					+ "/cometd", transport);
			client.getChannel("/**").addListener(new MessageLogger());

			client.handshake();
			client.getChannel("/service/**").addListener(new MessageParser());
			client.getChannel("/do/**").addListener(new MessageParser());
			client.getChannel("/get/**").addListener(new MessageParser());

			client.getChannel(Channel.META_HANDSHAKE).addListener(new ClientSessionChannel.MessageListener() 
			{ 
				public void onMessage(ClientSessionChannel channel, Message message)
				{
					if (message.isSuccessful())
					{
						log.info("handshaking ok");
						WhoAmI whoami = WhoAmI.newBuilder().setClientType(ClientType.Alex)
								.setDocumentType(DocType.Spreadsheet)
								.setEnvironmentType(EnvironmentType.Desktop).build();
						sendMessage("/service/alex/register", whoami);
					}
				}
			});
		} catch (Exception e) {
			log.debug(e.getMessage());
		}
	}

}
