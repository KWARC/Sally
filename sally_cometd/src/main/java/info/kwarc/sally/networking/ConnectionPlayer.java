package info.kwarc.sally.networking;

import info.kwarc.sally.networking.interfaces.IConnectionManager;

import java.io.IOException;
import java.io.Reader;

import org.codehaus.jackson.JsonNode;
import org.codehaus.jackson.JsonParseException;
import org.codehaus.jackson.map.JsonMappingException;
import org.codehaus.jackson.map.ObjectMapper;

import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.protobuf.AbstractMessage;

public class ConnectionPlayer {
	Reader in;
	IConnectionManager realManager;


	public ConnectionPlayer(Reader in) {
		this.in = in;
	}

	public void start(IConnectionManager realManager) {
		ObjectMapper mapper = new ObjectMapper();
		try {
			JsonNode rootNode = mapper.readValue(in, JsonNode.class);
			for (JsonNode node : rootNode) {
				if (node.get("type").asText().equals("newClient")) {
					realManager.newClient(node.get("client").asText());
					continue;
				}
				if (node.get("type").asText().equals("newMessage")) {
					String msg = node.get("msgObj").toString();
					AbstractMessage absmsg = ProtoUtils.deserialize(msg);
					if (absmsg == null) 
						continue;
					realManager.newMessage(node.get("client").asText(), absmsg);
					continue;
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
