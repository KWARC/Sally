package info.kwarc.sally.sharejs;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URLConnection;

import org.apache.commons.io.IOUtils;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

public class TextSnapshot extends AbstractSnapshot{
	String snapshot;
	ShareJS shareJS;

	private TextSnapshot(ShareJS sharejs, String collection, String fileName, long version) {
		super(version, collection, fileName);
		this.shareJS = sharejs;
		System.out.println("ver = "+version);
	}

	private void setSnapshot(String snapshot) {
		this.snapshot = snapshot;
	}

	public static TextSnapshot create(ShareJS shareJS, String collection, String fileName, String content) {
		JSONObject jsonData=new JSONObject();
		jsonData.put("type", ShareJS.textType);
		jsonData.put("data", content);
		JSONObject request = new JSONObject();
		request.put("create", jsonData);
		URLConnection conn = shareJS.postOp(collection, fileName, request.toJSONString());
		Long version = shareJS.getVersion(conn) + 1;
		System.out.println("Create version "+version);
		TextSnapshot snap = new TextSnapshot(shareJS, collection, fileName, version);
		snap.setSnapshot(content);
		return snap;
	}

	public void insertText(int offset, String text) {
		JSONArray opSpec = new JSONArray();
		if (offset > 0) {
			opSpec.add(offset);
		}
		opSpec.add(text);

		JSONObject op = new JSONObject();
		op.put("v", getVersion());
		op.put("op", opSpec);
		URLConnection conn = shareJS.postOp(getCollection(), getFileName(), op.toJSONString());
		this.version = shareJS.getVersion(conn) + 1;
		
		ByteArrayOutputStream writer = new ByteArrayOutputStream();
		try {
			IOUtils.copy(conn.getInputStream(), writer);
		} catch (IOException e) {
			e.printStackTrace();
		}
		String rest = writer.toString();
		System.out.println("need to do " +version+" - " + rest);
	}

	public void removeText(int offset, int len) {
		JSONArray opSpec = new JSONArray();
		if (offset > 0) {
			opSpec.add(offset);
		}
		JSONObject del = new JSONObject();
		del.put("d", len);
		opSpec.add(del);

		JSONObject op = new JSONObject();
		op.put("v", getVersion());
		op.put("op", opSpec);
		URLConnection conn = shareJS.postOp(getCollection(), getFileName(), op.toJSONString());
		this.version = shareJS.getVersion(conn) + 1;
		
		ByteArrayOutputStream writer = new ByteArrayOutputStream();
		try {
			IOUtils.copy(conn.getInputStream(), writer);
		} catch (IOException e) {
			e.printStackTrace();
		}
		String rest = writer.toString();
		System.out.println("need to do " +version+" - " + rest);
	}

	static TextSnapshot parse(ShareJS shareJS, String collection, String fileName, long version, InputStream response) {
		TextSnapshot result = new TextSnapshot(shareJS, collection, fileName, version);

		ByteArrayOutputStream writer = new ByteArrayOutputStream();
		try {
			IOUtils.copy(response, writer);
		} catch (IOException e) {
			e.printStackTrace();
		}
		result.setSnapshot(writer.toString());
		return result;
	}

}
