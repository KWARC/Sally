package info.kwarc.sally.planetary;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import org.apache.xmlrpc.XmlRpcException;
import org.apache.xmlrpc.XmlRpcRequest;
import org.apache.xmlrpc.client.XmlRpcClient;
import org.apache.xmlrpc.client.XmlRpcClientConfigImpl;
import org.apache.xmlrpc.client.XmlRpcClientException;
import org.apache.xmlrpc.client.XmlRpcSunHttpTransport;
import org.apache.xmlrpc.client.XmlRpcSunHttpTransportFactory;
import org.apache.xmlrpc.client.XmlRpcTransport;
import org.apache.xmlrpc.client.XmlRpcTransportFactory;
import org.slf4j.Logger;

import sally.Cookie;
import sally.MMTUri;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

@Singleton
public class Planetary {
	String sessionCookie;
	ISallyKnowledgeBase kb;
	
	@Inject
	public Planetary(@Named("PlanetaryURL")String planetaryRoot, 
					 @Named("PlanetaryEndPoint") String endPoint, 
					 @Named("PlanetaryUser") String user, 
					 @Named("PLanetaryPassword") String password,
					 Theo theo,
					 ISallyKnowledgeBase kb) {
		endpointURL = planetaryRoot+"/"+endPoint;
		this.kb = kb;
		this.root = planetaryRoot;
		this.user = user;
		this.password = password;
		this.theo = theo;
	}

	static final String METHOD_SYSTEM_CONNECT = "system.connect";
	static final String METHOD_USER_LOGOUT = "user.logout";
	static final String METHOD_USER_LOGIN = "user.login";
	static final String METHOD_SALLY_ENABLE = "sally.jobad_service";
	
	private Logger log;
	private String endpointURL;
	private XmlRpcClient xmlRpcClient;
	String user; 
	String password;
	String root;
	Theo theo;
	
	public String getDefinitionLookupURL(String mmtURI) {
		String [] splits = mmtURI.split("\\?");
		return root+"/sally/showdef/"+splits[1]+"/"+splits[2];
	}
	
	@SallyService
	public void getServiceURI(ListOntologyConcepts request, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		String cookie = getSessionCookie();
		context.setContextVar("Cookie", Cookie.newBuilder().setCookie(cookie).setUrl(root).build());
		acceptor.acceptResult(root);
	}
	
	@SallyService
	public void planetaryServices(final MMTUri mmtURI, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Definition Lookup", "Look up definition associated to the selected object") {
			public void run() {
				Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);

				HashMap<String, Object>  input = new  HashMap<String, Object>();
				input.put("wndURLInput", getDefinitionLookupURL(mmtURI.getUri()));
				kb.startProcess(parentProcessInstanceID, "Sally.deflookup", input);
			}
		});

		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Semantic Navigation", "Navigate dependencies associated to the selected object") {
			public void run() {			
			}
		});
	}

	public void connect() throws Exception {
		try {
			xmlRpcClient.execute(METHOD_SYSTEM_CONNECT, new Object[]{});
		} catch (Exception x) {
			throw new Exception("cannot connect to " + endpointURL + ": " + x.getMessage());
		}
	}

	public String login(String username, String password) throws Exception {
		// Add Login Paramaters
		Vector<Object> params = new Vector<Object>();
		params.add(username);
		params.add(password);
		Map<String, String> response = (Map<String, String>) xmlRpcClient.execute(METHOD_USER_LOGIN, params);

		//The user.login call return two attributes in which we use to construct value for a "Cookie" header.
		//With then set xmlRpcClient with new XmlRpcTransportFactory that set  'Cookie' header using the composed cookie value
		sessionCookie = response.get("session_name") + "=" + response.get("sessid");

		XmlRpcTransportFactory factory = new XmlRpcSunHttpTransportFactory(xmlRpcClient) {
			public XmlRpcTransport getTransport() {
				return new XmlRpcSunHttpTransport(xmlRpcClient) {
					@Override
					protected void initHttpHeaders(XmlRpcRequest request) throws XmlRpcClientException {
						super.initHttpHeaders(request);
						setRequestHeader("Cookie", sessionCookie);
					}
				};
			}
		};
		xmlRpcClient.setTransportFactory(factory);

		return sessionCookie;
	}

	public void logout() {
		Vector<Object> params = new Vector<Object>();
		try {
			xmlRpcClient.execute(METHOD_USER_LOGOUT, params);
		} catch (XmlRpcException e) {
			e.printStackTrace();
			return;
		}
		log.debug("Logout Sucessfull");
		sessionCookie = null;
	}


	public void enable_sally(String service) {
		try {
			Vector<Object> params = new Vector<Object>();
			params.add("enable");
			params.add(service);
			xmlRpcClient.execute(METHOD_SALLY_ENABLE, params);
		} catch (Exception E) {

		}
	}

	public String getSessionCookie() {
		if (sessionCookie != null) {
			return sessionCookie;
		}

		XmlRpcClientConfigImpl config = new XmlRpcClientConfigImpl();
		try {
			config.setServerURL(new URL(endpointURL));
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}
		xmlRpcClient = new XmlRpcClient();
		xmlRpcClient.setConfig(config);

		try {
			connect();
			String cookie = login(user, password);
			return cookie;
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}

}
