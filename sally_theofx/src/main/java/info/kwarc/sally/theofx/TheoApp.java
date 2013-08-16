package info.kwarc.sally.theofx;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.theofx.ui.TheoWindow;
import javafx.application.Platform;
import javafx.scene.web.WebEngine;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.Cookie;

import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.protobuf.AbstractMessage;

/**
 * Class for allowing interaction from javascript
 */

public class TheoApp {

	public Logger loggr;
	private int pid;
	
	public TheoApp(int pid) {
		this.loggr = LoggerFactory.getLogger(TheoWindow.class);
		this.pid = pid;
	}
	
	//For Tests
	/*TheoApp() {
		this.loggr = LoggerFactory.getLogger(TheoWindow.class);
	}*/
	
	
	public void applogger(String loginfo){
		this.loggr.debug(loginfo);
	}
	
	public void exit() {
        Platform.exit();
    }
	
	
	
	public void injectScripts() // communication to content
	{
		loggr.info("Injecting scripts");
		
		
		String scriptsToInject = "[\"communication.js\",\"comm/dataview.js\",\"comm/protobuf.js\",\"comm/common.js\",\"comm/util.js\"]";
		loggr.info(scriptsToInject.toString());
		
		WebEngine contentEngine = TheoWindow.content.getEngine();
		
		/*Element element = doc.createElement("ReceivedElement");
		doc.getDocumentElement().appendChild(element);*/
		
		contentEngine.executeScript("var element = document.createElement(\"ReceivedElement\");" +
				"document.documentElement.appendChild(element); ");
/*		contentEngine.executeScript("var evt = document.createEvent(\"Events\");" +
									"evt.initEvent(\"ReceivedScripts\", true, false);" +
									"element.dispatchEvent(evt);");*/
		contentEngine.executeScript("var event = new CustomEvent(\"ReceivedScripts\", {"+
				"detail : "+scriptsToInject.toString() +","+
				"bubbles : true,"+
				"cancelable : false	});");
		contentEngine.executeScript("element.dispatchEvent(event)");

		loggr.info("Inject script procedure complete");

	}
	
	
	
//	//This guy sends the above result back to Communication.sendMessage from communication.js
	public void sendBack(AbstractMessage result){
		//somehow send this back to javascript
		//TODO get the new ProtoUtils, remove = "";// from below line
		String jsReadyResult = ProtoUtils.serialize(result).toString();
		
		WebEngine contentEngine = TheoWindow.content.getEngine();
		contentEngine.executeScript("var element = document.createElement(\"TheoResultElement\");"+
									"document.documentElement.appendChild(element);"); 

		contentEngine.executeScript(
				"var event = new CustomEvent(\"TheoResult\", { " +
																"detail : "+ jsReadyResult.toString() +"," +
																"bubbles : true," +
																"cancelable : false " +
															 "});"
									);
		loggr.debug("Second exec");
		contentEngine.executeScript("element.dispatchEvent(event);");
		loggr.debug("Last exec");

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
	
	
	public void openNewWindow(Long pid, int sizeX, int sizeY, int posX,
			int posY, String stageTitle, String url, Cookie cookies, boolean visible) {
		TheoWindow.addWindow(pid, sizeX, sizeY , posX, posY, "Theo", url, cookies, visible);
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