package info.kwarc.sally.networking;

import java.io.FileWriter;
import java.io.IOException;

import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.protobuf.AbstractMessage;
import com.sun.syndication.io.impl.Base64;

import info.kwarc.sally.networking.interfaces.IConnectionManager;

public class ConnectionRecorder implements IConnectionManager {
	FileWriter fw;
	IConnectionManager realManager;

	public ConnectionRecorder(FileWriter fw, IConnectionManager realManager) {
		this.fw = fw;
		this.realManager = realManager;
		try {
			fw.append("[\n");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void close() {
		try {
			fw.append("{\t\"type\":\"end\"}]\n");
			fw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public void newClient(String clientID) {
		try {
			fw.append("{");
			fw.append("\t\"type\":\"newClient\",");
			fw.append("\t\"client\":\""+clientID+"\"");
			fw.append("},\n");
			fw.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		realManager.newClient(clientID);
	}

	@Override
	public void newMessage(String clientID, String type, Object data) {
		try {
			fw.append("{");
			fw.append("\t\"type\":\"newMessage\",");
			fw.append("\t\"client\":\""+clientID+"\",");
			fw.append("\t\"msgType\":\""+type+"\",");
			fw.append("},\n");
			fw.flush();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		realManager.newMessage(clientID, type, data);

	}

	@Override
	public void newMessage(String clientID, AbstractMessage msg) {
		
		try {
			fw.append("{");
			fw.append("\t\"type\":\"newMessage\",");
			fw.append("\t\"client\":\""+clientID+"\",");
			fw.append("\t\"msgObj\":"+ProtoUtils.serialize(msg));
			fw.append("},\n");
			fw.flush();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		realManager.newMessage(clientID, msg);
	}

	@Override
	public void disconnect(String clientID) {
		try {
			fw.append("{");
			fw.append("\t\"type\":\"disconnect\",");
			fw.append("\t\"client\":\""+clientID+"\",");
			fw.append("},\n");
			fw.flush();} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		realManager.disconnect(clientID);		
	}

}
