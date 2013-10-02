package info.kwarc.sally.networking;

import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.networking.interfaces.MockNetworkSender;

import java.io.IOException;
import java.io.Reader;

import org.codehaus.jackson.JsonNode;
import org.codehaus.jackson.JsonParseException;
import org.codehaus.jackson.map.JsonMappingException;
import org.codehaus.jackson.map.ObjectMapper;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.protobuf.AbstractMessage;

public class ConnectionPlayer {
	Reader in;
	IConnectionManager connectionManager;
	Logger log;

	@Inject
	public ConnectionPlayer(@Assisted Reader in, IConnectionManager connectionManager) {
		this.in = in;
		log = LoggerFactory.getLogger(getClass());
		this.connectionManager = connectionManager;
	}

	public void start() {
		ObjectMapper mapper = new ObjectMapper();
		try {
			JsonNode rootNode = mapper.readValue(in, JsonNode.class);
			for (JsonNode node : rootNode) {
				if (node.get("type").asText().equals("newClient")) {
					String client = node.get("client").asText();
					log.info("new client "+client);
					connectionManager.newClient(client, new MockNetworkSender());
					continue;
				}
				if (node.get("type").asText().equals("newMessage")) {
					String client = node.get("client").asText();
					log.info("new msg "+client+ " "+ node.get("msgObj").get("type"));

					String msg = node.get("msgObj").toString();
					AbstractMessage absmsg = ProtoUtils.deserialize(msg);
					log.info(absmsg.toString());
					if (absmsg != null) 
						connectionManager.newMessage(node.get("client").asText(), absmsg);
				}
			}
		} catch (JsonParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (JsonMappingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} // src can be a File, URL, InputStream etc

	}
}
