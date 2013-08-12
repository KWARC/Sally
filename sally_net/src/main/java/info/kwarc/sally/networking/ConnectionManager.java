package info.kwarc.sally.networking;

import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sissi.bpm.BPMNUtils;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.util.HashMap;

import org.drools.runtime.process.ProcessInstance;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.protobuf.AbstractMessage;

@Singleton
public class ConnectionManager implements IConnectionManager {
	
	Logger log;

	HashMap<String, ProcessInstance> sessions;
	HashMap<Long, String> processToSession;
	ISallyKnowledgeBase knowledgeBase;
	
	@Inject
	public ConnectionManager(ISallyKnowledgeBase knowledgeBase) throws Exception {
		this.knowledgeBase = knowledgeBase;
		sessions = new HashMap<String, ProcessInstance>();
		log = LoggerFactory.getLogger(this.getClass());
		processToSession = new HashMap<Long, String>();
	}
	
	@Provides
	public INetworkSender getSenderStrategy() {
		return null;
	}
	
	public ProcessInstance getState(String clientID) {
		return sessions.get(clientID);
	}
	
	/* (non-Javadoc)
	 * @see info.kwarc.sally.networking.IConnectionManager#newClient(java.lang.String)
	 */
	@Override
	public void newClient(String clientID) {
		if (sessions.containsKey(clientID))
			return;
		HashMap<String, Object> params = new HashMap<String, Object>();
		params.put("ConnectionIDInput", clientID);
		ProcessInstance instance = knowledgeBase.startProcess(null, "Sally.connect", params);
		processToSession.put(instance.getId(), clientID);
		sessions.put(clientID, instance);
	}
	
	/* (non-Javadoc)
	 * @see info.kwarc.sally.networking.IConnectionManager#newMessage(java.lang.String, java.lang.String, java.lang.Object)
	 */
	@Override
	public void newMessage(String clientID, String type, Object data) {
		ProcessInstance sess = sessions.get(clientID);
		if (sess == null) {
			log.debug("Client "+clientID+" does not have an active session. Ignoring.");
			return;
		}
		BPMNUtils.sendMessageOrForward(sess, type, data);
	}

	/* (non-Javadoc)
	 * @see info.kwarc.sally.networking.IConnectionManager#newMessage(java.lang.String, com.google.protobuf.AbstractMessage)
	 */
	@Override
	public void newMessage(String clientID, AbstractMessage msg) {
		newMessage(clientID, "Message-"+msg.getClass().getSimpleName(), msg);
	}
	
	/* (non-Javadoc)
	 * @see info.kwarc.sally.networking.IConnectionManager#disconnect(java.lang.String)
	 */
	@Override
	public void disconnect(String clientID) {
		
	}

}
