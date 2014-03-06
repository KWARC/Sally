package info.kwarc.sally.core.workflow;

import java.util.Map;

public class WorkflowUtils {
	public static <T> T getFirstTypedParameter(Map<String, Object> params, Class<T> cls) {
		for (String param : params.keySet()) {
			if (param.endsWith("Input") && cls.isAssignableFrom(params.get(param).getClass())) {
				return cls.cast(params.get(param));
			}
		}
		return null;
	}
	
	public static <T> T safeGet(Map<String, Object> map, String key, Class<T> cls) {
		Object t = map.get(key);
		if (t==null)
			return null;
		if (cls.isAssignableFrom(t.getClass())) {
			return (T) t;
		}			
		return null;
	}
}
