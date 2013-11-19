package info.kwarc.sally.sharejs;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLEncoder;

import org.apache.commons.io.IOUtils;

public class ShareJS {
	String baseUrl;
	String charset = "UTF-8";
	
	public static final String textType = "http://sharejs.org/types/textv1";
	public static final String jsonType = "http://sharejs.org/types/json";

	public ShareJS(String url) {
		this.baseUrl = url;
	}

	protected Long getVersion(URLConnection connection) {
		Long otVersion = Long.parseLong(connection.getHeaderField("X-OT-Version"));
		return otVersion;
	}
	
	URLConnection getConn(String collection, String document, String reqMethod) throws MalformedURLException, IOException {
		String url = String.format("%s/doc/%s/%s", baseUrl, URLEncoder.encode(collection, charset), URLEncoder.encode(document, charset));
		URLConnection conn = new URL(url).openConnection();
		conn.setRequestProperty("Content-Type", "application/json");
		conn.setDoOutput(true);

		HttpURLConnection conn2 = (HttpURLConnection) conn;

		conn2.setRequestMethod(reqMethod);
		return conn;
	}
	
	void printError(URLConnection conn) {
		try {
			System.out.println("Error: "+IOUtils.toString(((HttpURLConnection)conn).getErrorStream()));
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	void addRequestData(URLConnection conn, String data) {
		OutputStream str;
		try {
			str = conn.getOutputStream();
			str.write(data.getBytes());
			str.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public AbstractSnapshot getSnapshot(String collection, String document) {
		URLConnection connection;
		try {
			connection = getConn(collection, document, "GET");
			InputStream response = connection.getInputStream();

			int status = ((HttpURLConnection )connection).getResponseCode();
			if (status != 200)
				return null;

			String otType = connection.getHeaderField("X-OT-Type");
			Long otVersion = Long.parseLong(connection.getHeaderField("X-OT-Version"));
			if (otType.equals(textType)) {
				return TextSnapshot.parse(this, collection, document, otVersion, response);
			}
			return null;
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	public boolean existFile(String collection, String document) {
		URLConnection connection;
		try {
			connection = getConn(collection, document, "HEAD");

			int status = ((HttpURLConnection )connection).getResponseCode();
			if (status != 200)
				return false;
			return true;
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
		}
		return false;
	}

	public void deleteFile(String collection, String document) {
		URLConnection connection = null;
		try {
			connection = getConn(collection, document, "DELETE");
			connection.getInputStream();
		} catch (MalformedURLException e) {
			e.printStackTrace();
		} catch (IOException e) {
			printError(connection);
		}
	}

	public URLConnection postOp(String collection, String document, String op) {
		URLConnection conn = null;
		System.out.println("sending " +op);
		try {
			conn = getConn(collection, document, "POST");
			addRequestData(conn , op);
			conn.getInputStream();
		} catch (MalformedURLException e) {
			e.printStackTrace();
		} catch (IOException e) {
			printError(conn);
		}
		return conn;
	}

	public static void main(String[] args) {
		ShareJS s = new ShareJS("http://localhost:7007");
		if (!s.existFile("users", "jeremy")) {
			TextSnapshot.create(s, "users", "jeremy", "Hello there");
		} else {
			s.deleteFile("users", "jeremy");
		}
	}
}
