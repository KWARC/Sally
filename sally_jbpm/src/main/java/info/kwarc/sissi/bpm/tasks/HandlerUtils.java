package info.kwarc.sissi.bpm.tasks;

import java.util.HashMap;
import java.util.Map;

import org.drools.runtime.process.WorkItemManager;

import com.google.protobuf.AbstractMessage;
import com.google.protobuf.Descriptors.FieldDescriptor;

public class HandlerUtils {
	public static String guessOutputName(Map<String, Object> params) {
		for (String param : params.keySet()) {
			if (param.endsWith("Output")) {
				return param;
			}
		}
		return null;
	}
	
	public static HashMap<String, TestCounterHandler> registerCounterHandlers(WorkItemManager manager, String ...handlers) {
		HashMap<String, TestCounterHandler> result = new HashMap<String, TestCounterHandler>();
		for (String handler : handlers) {
			TestCounterHandler counterHandler = new TestCounterHandler();
			manager.registerWorkItemHandler(handler, counterHandler);
			result.put(handler, counterHandler);
		}
		return result;
	}

	public static String getFileNameFromMessage(AbstractMessage msg) {
		for (FieldDescriptor fld :  msg.getAllFields().keySet()) {
			if (fld.getName().equals("fileName")) {
				return msg.getField(fld).toString();
			}
		}
		return null;
	}
	
	public static <T> T getFirstTypedParameter(Map<String, Object> params, Class<T> cls) {
		for (String param : params.keySet()) {
			if (param.endsWith("Input") && cls.isAssignableFrom(params.get(param).getClass())) {
				return cls.cast(params.get(param));
			}
		}
		return null;
	}
}
