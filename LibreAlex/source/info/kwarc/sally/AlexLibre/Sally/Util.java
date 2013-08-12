package info.kwarc.sally.AlexLibre.Sally;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.binary.Base64;
import org.cometd.bayeux.Message;

import com.google.protobuf.AbstractMessage;
import com.google.protobuf.GeneratedMessage;

public class Util {
	public static AbstractMessage restoreMessage(Message message) {
		String type = (String)message.get("type");
		String s = (String)message.get("s");
		if (type == null || s == null)
			return null;
		return Util.stringToProto(type, s);
	}
	
	public static Map<String, Object> prepareMessage(AbstractMessage message) {
		Map<String, Object> output = new HashMap<String, Object>();
		if (message!=null) {
			output.put("type", message.getClass().getName());
			output.put("s", Base64.encodeBase64String(message.toByteArray()));
		}
		return output;
	}

	public static AbstractMessage stringToProto(String type, String message) {
		String classString = type;
		try {
			Class<?> t;
			t = Class.forName(classString);
			if (t == null) {
				return null;
			}
			if (!t.getSuperclass().equals(GeneratedMessage.class)) {
				return null; 
			}
			String restMessage = message;
			byte [] binaryData = Base64.decodeBase64(restMessage);

			Object result = t.getMethod("parseFrom", byte[].class).invoke(null, binaryData);
			if (result == null)
				return null;

			return (AbstractMessage) result;
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
}
