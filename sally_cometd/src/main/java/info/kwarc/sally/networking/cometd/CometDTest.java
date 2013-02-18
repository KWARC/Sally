package info.kwarc.sally.networking.cometd;

import java.util.HashMap;
import java.util.Map;

import junit.framework.Assert;

import org.cometd.bayeux.Message;
import org.cometd.bayeux.client.ClientSessionChannel;
import org.cometd.bayeux.server.ServerChannel;
import org.cometd.bayeux.server.ServerChannel.MessageListener;
import org.cometd.bayeux.server.ServerSession;
import org.cometd.bayeux.server.ServerMessage.Mutable;
import org.cometd.client.BayeuxClient;
import org.cometd.client.BayeuxClient.State;
import org.cometd.client.transport.ClientTransport;
import org.cometd.client.transport.LongPollingTransport;
import org.cometd.server.AbstractService;
import org.eclipse.jetty.client.HttpClient;
import org.junit.Before;
import org.junit.Test;

public class CometDTest {
	CometD server;
	int sentSuccesfully;
	
	@Before
	public void setup() {
		server = new CometD(8080);
		server.start();
		server.registerListener("/service/echo", new MessageListener() {
			public boolean onMessage(ServerSession from, ServerChannel channel,
					Mutable message) {
				from.deliver(from, message.getChannel(), message.toString(), message.getId());
				return true;
			}
		});
	}
	
	public class CommTester implements ClientSessionChannel.MessageListener {
		public void onMessage(ClientSessionChannel arg0, Message arg1) {
			sentSuccesfully++;
		}
	}
	
	@Test
	public void test() {
		HttpClient httpClient = new HttpClient();
		try {
			httpClient.start();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		// Prepare the transport
		Map<String, Object> options = new HashMap<String, Object>();
		ClientTransport transport = LongPollingTransport.create(options, httpClient);

		BayeuxClient bayeuxClient = new BayeuxClient("http://localhost:8080/sally/cometd", transport);
		
		bayeuxClient.getChannel("/service/echo").addListener(new CommTester());

		bayeuxClient.handshake();
		sentSuccesfully = 0;
		bayeuxClient.getChannel("/service/echo").publish("{str:'test'}");
		
		bayeuxClient.waitFor(100, State.DISCONNECTED);
		Assert.assertEquals(2, sentSuccesfully);
	}

}
