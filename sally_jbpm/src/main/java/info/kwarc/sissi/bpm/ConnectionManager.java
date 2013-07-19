package info.kwarc.sissi.bpm;

import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.util.HashMap;

import org.drools.runtime.process.ProcessInstance;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.protobuf.AbstractMessage;

@Singleton
public class ConnectionManager {
	
	Logger log;

	HashMap<String, ProcessInstance> sessions; 
	ISallyKnowledgeBase knowledgeBase;
	
	@Inject
	public ConnectionManager(ISallyKnowledgeBase knowledgeBase) throws Exception {
		this.knowledgeBase = knowledgeBase;
		sessions = new HashMap<String, ProcessInstance>();
		log = LoggerFactory.getLogger(this.getClass());
	}
	
	protected ProcessInstance getState(String clientID) {
		return sessions.get(clientID);
	}
	
	public void newClient(String clientID) {		;
		sessions.put(clientID, knowledgeBase.startProcess("info.kwarc.jbpm.connect"));
	}
	
	public void newMessage(String clientID, String type, Object data) {
		ProcessInstance sess = sessions.get(clientID);
		if (sess == null) {
			log.debug("Client "+clientID+" does not have an active session. Ignoring.");
			return;
		}
		sess.signalEvent(type, data);
	}

	public void newMessage(String clientID, AbstractMessage msg) {
		newMessage(clientID, msg.getClass().getCanonicalName(), msg);
	}
}
