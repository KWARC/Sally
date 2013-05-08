package info.kwarc.sally.planetary;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;

import java.net.MalformedURLException;
import java.net.URL;
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
import sally.ScreenCoordinates;
import sally.TheoOpenWindow;

public class Planetary {
	String sessionCookie;

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
	
	public String getDefinitionLookupURL(String mmtURI) {
		String [] splits = mmtURI.split("\\?");
		return root+"/sally/showdef/"+splits[1]+"/"+splits[2];
	}
	
	@SallyService
	public void getServiceURI(ListOntologyConcepts request, SallyActionAcceptor acceptor, final SallyContext context) {
		String cookie = getSessionCookie();
		context.setContextVar("Cookie", Cookie.newBuilder().setCookie(cookie).setUrl(root).build());
		acceptor.acceptResult(root);
	}
	
	@SallyService
	public void planetaryServices(final MMTUri mmtURI, SallyActionAcceptor acceptor, final SallyContext context) {
		ScreenCoordinates coords;
		if (context.getContextVar("preferred_position") instanceof ScreenCoordinates) {
			coords = (ScreenCoordinates) context.getContextVar("preferred_position");
		} else {
			coords = ScreenCoordinates.newBuilder().setX(200).setY(400).build();
		}
		
		final TheoOpenWindow.Builder openWindow = TheoOpenWindow
				.newBuilder()
				.setSizeX(500).setSizeY(350)
				.setPosition(coords);
	
		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Definition Lookup") {
			public void run() {			
				openWindow.setTitle("Definition Lookup").setUrl(getDefinitionLookupURL(mmtURI.getUri()));
				context.getCurrentInteraction().getOneInteraction(openWindow.build(), Boolean.class);
				System.out.println("Doing definition lookup "+ openWindow.build());
			}
		});

		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Semantic Navigation") {
			public void run() {			
				openWindow.setTitle("Definition Lookup").setUrl(getDefinitionLookupURL(mmtURI.getUri()));
				context.getCurrentInteraction().getOneInteraction(openWindow.build(), Boolean.class);
				System.out.println("Doing definition lookup "+ openWindow.build());
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

	public Planetary(String planetaryRoot, String endPoint, String user, String password) {
		endpointURL = planetaryRoot+"/"+endPoint;
		this.root = planetaryRoot;
		this.user = user;
		this.password = password;
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
