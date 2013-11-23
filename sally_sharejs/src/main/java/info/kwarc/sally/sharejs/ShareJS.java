package info.kwarc.sally.sharejs;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLEncoder;

import org.apache.commons.io.IOUtils;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.inject.Inject;
import com.google.inject.name.Named;

public class ShareJS implements IDocManager {
	String baseUrl;
	String charset = "UTF-8";
	ObjectMapper mapper; 

	@Inject
	public ShareJS(@Named("ShareJSURL") String url) {
		this.baseUrl = url;
		mapper = new ObjectMapper();
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

	/* (non-Javadoc)
	 * @see info.kwarc.sally.sharejs.IDocManager#existFile(java.lang.String, java.lang.String)
	 */
	@Override
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

	/* (non-Javadoc)
	 * @see info.kwarc.sally.sharejs.IDocManager#deleteFile(java.lang.String, java.lang.String)
	 */
	@Override
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

	public ISyncResult sendOp(String collection, String document, IDocumentOp op) {
		URLConnection conn = null;
		String serializedOp;

		try {
			serializedOp = mapper.writeValueAsString(op);
			System.out.println(serializedOp);
			conn = getConn(collection, document, "POST");
			addRequestData(conn , serializedOp);
			conn.getInputStream();
		} catch (MalformedURLException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
			printError(conn);
		}
		Long version = getVersion(conn);

		return new ISyncResult(version);
	}

	@Override
	public ISyncResult createDoc(String collection, String document, String docType, String content) {
		return sendOp(collection, document, new DocumentCreateRequest().setData(content).setType(docType));
	}

	@Override
	public ISyncResult getSnapshot(String collection, String document, AbstractSnapshot snapshot) {
		URLConnection connection;
		try {
			connection = getConn(collection, document, "GET");
			InputStream response = connection.getInputStream();

			int status = ((HttpURLConnection )connection).getResponseCode();
			if (status != 200)
				return null;

			String otType = connection.getHeaderField("X-OT-Type");
			Long otVersion = Long.parseLong(connection.getHeaderField("X-OT-Version"));
			
			ByteArrayOutputStream writer = new ByteArrayOutputStream();
			IOUtils.copy(response, writer);
			snapshot.setSnapshot(otType, writer.toString());
			
			return new ISyncResult(otVersion);
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
}
