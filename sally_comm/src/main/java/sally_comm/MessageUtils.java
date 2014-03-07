package sally_comm;

import sally.WhoAmI;
import sally.WhoAmI.ClientType;
import sally.WhoAmI.EnvironmentType;

import com.google.protobuf.AbstractMessage;
import com.google.protobuf.Descriptors.FieldDescriptor;
import com.google.protobuf.Message.Builder;

public class MessageUtils {
	public static WhoAmI createDesktopSpreadsheetAlex() {
		return WhoAmI.newBuilder().setClientType(ClientType.Alex).setEnvironmentType(EnvironmentType.Desktop).build();
	}

	public static WhoAmI createDesktopCADAlex() {
		return WhoAmI.newBuilder().setClientType(ClientType.Alex).setEnvironmentType(EnvironmentType.Desktop).build();
	}

	public static String getFileNameFromMessage(AbstractMessage msg) {
		for (FieldDescriptor fld :  msg.getAllFields().keySet()) {
			if (fld.getName().equals("fileName")) {
				return msg.getField(fld).toString();
			}
		}
		return null;
	}

	public static String getCallbackTokenFromMessage(AbstractMessage msg) {
		for (FieldDescriptor fld :  msg.getAllFields().keySet()) {
			if (fld.getName().equals("callbackToken")) {
				return msg.getField(fld).toString();
			}
		}
		return null;
	}

	public static AbstractMessage setCallbackTokenToMessage(AbstractMessage msg, Long callbackToken) {
		Builder b = msg.newBuilderForType();
		for (FieldDescriptor fld :  msg.getDescriptorForType().getFields()) {
			if (fld.getName().equals("callbackToken")) {
				b.setField(fld, callbackToken);
			} else
				if (msg.hasField(fld)) {
					b.setField(fld, msg.getField(fld));
				}
		}
		return (AbstractMessage) b.build();
	}

}
