package info.kwarc.sally.core;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SallyInteraction {
	HashMap<Class<?>, List<MethodExec>> map;
	Logger log;
	SallyContext context;
	
	class MethodExec {
		Object obj;
		Method m;

		MethodExec(Object obj, Method m) {
			this.obj = obj;
			this.m = m;
		}

		public void setMethod(Method m) {
			this.m = m;
		}

		public void setObject(Object obj) {
			this.obj = obj;
		}

		public Method getMethod() {
			return m;
		}

		public Object getObject() {
			return obj;
		}
		
		public void exec(Object obj2, SallyActionAcceptor acceptor, SallyContext context) {
			try {
				m.invoke(obj, obj2, acceptor, context);
			} catch (IllegalArgumentException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvocationTargetException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	public SallyInteraction() {
		map = new HashMap<Class<?>, List<MethodExec>>();
		log = LoggerFactory.getLogger(this.getClass());
		context = new SallyContext();
	}

	private void addToMap(Class<?> param, Object obj, Method m) {
		if (!map.containsKey(param))
			map.put(param, new ArrayList<MethodExec>());
		map.get(param).add(new MethodExec(obj, m));
	}

	public void registerServices(Object obj) {
		for (Method m : obj.getClass().getMethods()) {
			SallyService serviceAnnotation = m.getAnnotation(SallyService.class);
			if (serviceAnnotation == null)
				continue;
			Class<?>[] parameters =  m.getParameterTypes();
			if (parameters.length != 3) {
				log.error(String.format("Method %s.%s is not a valid SallyService. Param count != 3", obj.getClass().getName(),m.getName()));
				continue;
			}
			if (!SallyActionAcceptor.class.isAssignableFrom(parameters[1])) {
				log.error(String.format("Method %s.%s is not a valid SallyService. 2nd argument should be assignable to SallyActionAcceptor", obj.getClass().getName(),m.getName()));
				continue;
			}
			if (!SallyContext.class.isAssignableFrom(parameters[2])) {
				log.error(String.format("Method %s.%s is not a valid SallyService. 3rd argument should be assignable to SallyContext", obj.getClass().getName(),m.getName()));
				continue;
			}
			addToMap(parameters[0],obj, m);
		}
	}

	public <T> List<T> getPossibleInteractions(Object obj, final Class<T> expectType) {
		final ArrayList<T> choices = new ArrayList<T>();
		HashSet<Object> memoizer = new HashSet<Object>();
		Stack<Object> stack = new Stack<Object>();
		stack.add(obj);memoizer.add(obj);
		
		SallyActionAcceptor acceptor = new SallyActionAcceptor() {
			@SuppressWarnings("unchecked")
			public void acceptResult(Object obj) {
				if (expectType.isAssignableFrom(obj.getClass())) {
					choices.add((T) obj);
				} else {
					
				}
			}
		};
		
		while (!stack.empty()) {
			Object top = stack.pop();
			if (!map.containsKey(top.getClass()))
				continue;
			for (MethodExec choice : map.get(top.getClass())) {
				choice.exec(top, acceptor, context);
			}
		}
		return choices;
	}
}
