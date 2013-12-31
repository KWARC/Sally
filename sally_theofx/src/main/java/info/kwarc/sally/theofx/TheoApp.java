package info.kwarc.sally.theofx;

import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.theofx.ui.TheoWindow;
import info.kwarc.sissi.bpm.BPMNUtils;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;
import javafx.scene.web.WebEngine;
import netscape.javascript.JSObject;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally_comm.ProtoUtils;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.protobuf.AbstractMessage;

/**
 * Class for allowing interaction from javascript
 */

public class TheoApp {

	private Logger log;
	private Long processInstanceID;
	private ISallyWorkflowManager kb;
	private WebEngine webEngine;
	private CallbackManager callbackManager;

	@Inject
	public TheoApp(@Assisted Long processInstanceID, @Assisted WebEngine contentEngine, ISallyWorkflowManager kb, CallbackManager callbackManager) {
		this.log = LoggerFactory.getLogger(TheoWindow.class); 
		this.processInstanceID = processInstanceID;
		this.webEngine = contentEngine;
		this.callbackManager = callbackManager;
		this.kb = kb;
	}

	//For Tests
	/*TheoApp() {
		this.loggr = LoggerFactory.getLogger(TheoWindow.class);
	}*/


	public void log(String data){
		this.log.info(data);
	}

	public void injectScripts() // communication to content
	{

		String prefix = "http://localhost:8181/sally/";
		String [] scriptsToInject = new String[] {"comm/communication.js", "comm/dataview.js", "comm/protobuf.js", "comm/common.js", "comm/util.js" };
		
		for (String script : scriptsToInject) {
			String sc = "var newScript = document.createElement('script'); newScript.type = 'text/javascript'; newScript.src = '"+prefix+script+"';document.getElementsByTagName('head')[0].appendChild(newScript); ";
			webEngine.executeScript(sc);			
		}

		log.info("Injected scripts");

	}

	public void sendMessage(String msg) {
		sendMessage(msg, null);
	}
	
	private class CallbackRunner implements IMessageCallback {
		Long callback;
		
		public CallbackRunner(Long callback) {
			this.callback = callback;
		}

		@Override
		public void onMessage(AbstractMessage m) {
			JSObject wnd = (JSObject) webEngine.executeScript("window");
			JSObject comm = (JSObject) wnd.getMember("Communication");
			comm.call("runCallback", callback, ProtoUtils.serialize(m));
		}
	}
	
	public void sendMessage(String msg, String callback) {
		AbstractMessage absMsg;
		try {
			absMsg = ProtoUtils.deserialize(msg);
		} catch (Throwable e) {
			log.error(e.getMessage());
			return;
		}
		if (callback != null) {
			Long callbackID = callbackManager.registerCallback(new CallbackRunner(new Long(callback)));
			
			absMsg = HandlerUtils.setCallbackTokenToMessage(absMsg, callbackID);
		}

		if (absMsg == null) {
			log.info("could not deserialize "+msg);
		}
		
		BPMNUtils.sendMessageOrForward(processInstanceID, kb.getProcessInstance(processInstanceID), absMsg);
	}

	//	//This guy sends the above result back to Communication.sendMessage from communication.js
	public void sendBack(AbstractMessage result){
		//somehow send this back to javascript
		//TODO get the new ProtoUtils, remove = "";// from below line
		String jsReadyResult = ProtoUtils.serialize(result).toString();

		webEngine.executeScript("var element = document.createElement(\"TheoResultElement\");"+
				"document.documentElement.appendChild(element);"); 

		webEngine.executeScript(
				"var event = new CustomEvent(\"TheoResult\", { " +
						"detail : "+ jsReadyResult.toString() +"," +
						"bubbles : true," +
						"cancelable : false " +
						"});"
				);
		log.debug("Second exec");
		webEngine.executeScript("element.dispatchEvent(event);");
		log.debug("Last exec");

	}

	//TODO change how the message is parsed and sent back
	/*	public void sendMessage(String serializedChannel, String serializedMessage){
		loggr.debug(serializedMessage.getClass().toString());
		AbstractMessage protoContent = ProtoUtils.stringToProto("java.lang.String", serializedMessage);
		AbstractMessage result = this.sallyInteraction.getOneInteraction(serializedChannel, protoContent, AbstractMessage.class);
		sendBack(result);
	}*/


	class Message //extends AbstractMessage 
	{
		private AbstractMessage content;
		String type;
		Message(AbstractMessage content, String type){
			this.content = content;
			this.type = type;
		}
		public AbstractMessage getContent() {
			return content;
		}
		public String getType() {
			return type;
		}
	}
}


/**
 * Class for allowing interaction from javascript
 * @author Alex
 *
 */
/*private class TheoApp {

	public void openNewWindow(int pid, int sizeX, int sizeY, int posX,
			int posY, String stageTitle, String url, Cookie cookies, boolean visible) {
		addWindow(pid, sizeX, sizeY , posX, posY, "Theo", url, cookies, visible);
	}
}
 */
//Code graveyard
//injectScripts
/* JSObject jsWin = // getEngine().executeScript("alert();");
Document doc = TheoWindow.communication.getEngine().getDocument();
// Retrieve the head element of the document
Element head = (Element) doc.getElementsByTagName("head").item(0);
NodeList nodes = head.getElementsByTagName("script");
StringBuilder scriptsArray = new StringBuilder();
scriptsArray.append("[");
for (int i = 0; i < nodes.getLength(); i++) {
	Node src = nodes.item(i).getAttributes().getNamedItem("src");
	if (src != null
			&& 
			((src.getNodeValue().indexOf("protobuf.js") != -1 
			|| src.getNodeValue().indexOf("common.js") != -1)
			|| src.getNodeValue().indexOf("dataview.js") != -1 
			|| src.getNodeValue().indexOf("util.js") != -1))

		scriptsArray.append("\"" + src.getNodeValue() + "\",");
}

scriptsArray.deleteCharAt(scriptsArray.lastIndexOf(","));
scriptsArray.append("]");


System.out.println(scriptsArray.toString());
 */		


/*//ERR: netscape.javascript.JSException: SyntaxError: Expected token '}'
	@Deprecated
	public void sendToSally(String messageDetail){ //JSObject event //"detail : "+event.getMember("detail")+","
		//Document resourceRequester = TheoWindow.communication.getEngine().getDocument();
		loggr.info("sendToSally sequence started (Not a real test)");
		//var doc = window.content.document;
		WebEngine communicationEngine = TheoWindow.communication.getEngine();
		communicationEngine.executeScript("var relayEvent = document.createElement(\"Relay\");\r\n" + 
				"		document.documentElement.appendChild(relayEvent);");

		communicationEngine.executeScript(
				"var event = new CustomEvent(\"MessageRelay\", { " +
				"detail : "+messageDetail.toString() +"," +
				"bubbles : true," +
				"cancelable : false });"
											);	
		//communicationEngine.executeScript("relayEvent.dispatchEvent(event);");
		loggr.info("sendToSally sequence complete");
	}*/