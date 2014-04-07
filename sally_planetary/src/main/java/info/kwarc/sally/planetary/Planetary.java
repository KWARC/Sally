package info.kwarc.sally.planetary;

import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

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

import Sally.Cookie;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.inject.name.Named;

@Singleton
public class Planetary {
	String sessionCookie;
	String sessionID;

	ISallyWorkflowManager kb;

	@Inject
	public Planetary(@Named("PlanetaryURL")String planetaryRoot, 
			@Named("PlanetaryEndPoint") String endPoint, 
			@Named("PlanetaryUser") String user, 
			@Named("PLanetaryPassword") String password,
			ISallyWorkflowManager kb) {
		endpointURL = planetaryRoot+"/"+endPoint;
		this.kb = kb;
		this.root = planetaryRoot;
		this.user = user;
		this.password = password;
		init();
	}

	private void init() {
		xmlRpcClient = new XmlRpcClient();
		XmlRpcClientConfigImpl config = new XmlRpcClientConfigImpl();
		try {
			config.setServerURL(new URL(endpointURL));
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return;
		}
		xmlRpcClient.setConfig(config);
		XmlRpcTransportFactory factory = new XmlRpcSunHttpTransportFactory(xmlRpcClient) {
			public XmlRpcTransport getTransport() {
				return new XmlRpcSunHttpTransport(xmlRpcClient) {
					@Override
					protected void initHttpHeaders(XmlRpcRequest request) throws XmlRpcClientException {
						super.initHttpHeaders(request);
						if (sessionCookie != null)
							setRequestHeader("Cookie", sessionCookie);
						if (sessionID != null)
							setRequestHeader("X-CSRF-Token", sessionID);
					}
				};
			}
		};
		xmlRpcClient.setTransportFactory(factory);
	}
	
	static final String METHOD_SYSTEM_CONNECT = "system.connect";
	static final String METHOD_USER_LOGOUT = "user.logout";
	static final String METHOD_USER_LOGIN = "user.login";
	static final String METHOD_USER_TOKEN = "user.token";
	static final String METHOD_SALLY_ENABLE = "Sally.enable_jobad";
	static final String METHOD_MMT_DEPENDENCIES = "Sally.get_dependencies";

	private Logger log;
	private String endpointURL;
	private XmlRpcClient xmlRpcClient;
	String user; 
	String password;
	String root;

	public String getMMTTheoryDepencies(String mmtURI) {
		Vector<Object> params = new Vector<Object>();
		params.add(mmtURI);
		try {
			Object obj = xmlRpcClient.execute(METHOD_MMT_DEPENDENCIES, params);
			System.out.println(obj.getClass());
		} catch (XmlRpcException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
	
	public String getPlanetaryRoot() {
		return root;
	}

	@SallyService
	public void getServiceURI(ListOntologyConcepts request, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		String cookie = getSessionCookie();
		context.setContextVar("Cookie", Cookie.newBuilder().setCookie(cookie).setUrl(root).build());
		acceptor.acceptResult(root);
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
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private String getSession() {
		try {
			Vector<Object> params = new Vector<Object>();
			Map<String, String> response = (Map<String, String>) xmlRpcClient.execute(METHOD_USER_TOKEN, params);
			sessionID = response.get("token");
		} catch (Exception e) {
			e.printStackTrace();
		}
		return sessionID;
	}

	public String getSessionCookie() {
		if (sessionCookie != null) {
			return sessionCookie;
		}
	
		try {
			connect();
			String cookie = login(user, password);
			getSession();
			return cookie;
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}

}
