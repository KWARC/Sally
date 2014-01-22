package info.kwarc.sally.core.composition;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.inject.Singleton;

@Singleton
public class SallyInteraction {
	static class ChannelClass {
		String channel;
		Class<?> cls;
		
		public ChannelClass(String channel, Class<?> cls) {
			this.channel = channel;
			this.cls = cls;
		}
		
		public String getChannel() {
			return channel;
		}
		
		public Class<?> getCls() {
			return cls;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (!(obj instanceof ChannelClass)) {
				return false;
			}
			ChannelClass t = (ChannelClass) obj;
			return channel.equals(t.getChannel()) && cls.equals(t.getCls());
		}
		
		@Override
		public int hashCode() {
			return cls.hashCode()*5+channel.hashCode()*13;
		}
	}
	
	HashMap<ChannelClass, List<MethodExec>> map;
	Logger log;
	SallyContext context;
	
	public SallyContext getContext() {
		return context;
	}
	
	class MethodExec {
		Object obj;
		Method m;

		MethodExec(Object obj, Method m) {
			this.obj = obj;
			this.m = m;
			this.m.setAccessible(true);
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
		
		public void exec(Object obj2, SallyInteractionResultAcceptor acceptor, SallyContext context) {
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
		map = new HashMap<SallyInteraction.ChannelClass, List<MethodExec>>();
		log = LoggerFactory.getLogger(this.getClass());
		context = SallyContextManager.getInstance().getEmptyContext(this);
	}

	private void addToMap(SallyService annotation, Class<?> param, Object obj, Method m) {
		ChannelClass key = new ChannelClass(annotation.channel(), param);
		if (!map.containsKey(key))
			map.put(key, new ArrayList<MethodExec>());
		map.get(key).add(new MethodExec(obj, m));
	}
	
	private List<MethodExec> getServices(String channel, Class<?> cls) {
		ChannelClass key = new ChannelClass(channel, cls);
		if (map.containsKey(key))
			return map.get(key);
		else
			return new LinkedList<SallyInteraction.MethodExec>();
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
			if (!SallyInteractionResultAcceptor.class.isAssignableFrom(parameters[1])) {
				log.error(String.format("Method %s.%s is not a valid SallyService. 2nd argument should be assignable to SallyActionAcceptor", obj.getClass().getName(),m.getName()));
				continue;
			}
			if (!SallyContext.class.isAssignableFrom(parameters[2])) {
				log.error(String.format("Method %s.%s is not a valid SallyService. 3rd argument should be assignable to SallyContext", obj.getClass().getName(),m.getName()));
				continue;
			}
			addToMap(serviceAnnotation, parameters[0], obj, m);
		}
	}

	public <T> T getOneInteraction(Object obj, final Class<T> expectType) {
		List<T> response = getPossibleInteractions("/what", obj, expectType, 1);
		if (response.size()==0)
			return null;
		return response.get(0);
	}

	public <T> T getOneInteraction(String channel, Object obj, final Class<T> expectType) {
		List<T> response = getPossibleInteractions(channel, obj, expectType, 1);
		if (response.size()==0)
			return null;
		return response.get(0);
	}
	
	public <T> List<T> getPossibleInteractions(String channel, Object obj, final Class<T> expectType) {
		return getPossibleInteractions(channel, obj, expectType, 1000000);
	}

	public <T> List<T> getPossibleInteractions(Object obj, final Class<T> expectType) {
		return getPossibleInteractions("/what", obj, expectType, 1000000);
	}

	private <T> List<T> getPossibleInteractions(String channel, Object obj, final Class<T> expectType, final int limit) {
		final ArrayList<T> choices = new ArrayList<T>();
		if (obj == null)
			return choices;
		HashSet<Object> memoizer = new HashSet<Object>();
		Stack<Object> stack = new Stack<Object>();
		stack.add(obj);memoizer.add(obj);
		
		SallyInteractionResultAcceptor acceptor = new SallyInteractionResultAcceptor() {
			@SuppressWarnings("unchecked")
			public void acceptResult(Object obj) {
				if (choices.size() >= limit)
					return;
				if (obj == null)
					return;
				if (expectType.isAssignableFrom(obj.getClass())) {
					choices.add((T) obj);
				} else {
					
				}
			}
		};
		
		while (!stack.empty()) {
			Object top = stack.pop();
			if (choices.size() >= limit)
				break;
			for (MethodExec choice : getServices(channel, top.getClass())) {
				if (choices.size() >= limit)
					break;
				choice.exec(top, acceptor, context);
			}
		}
		return choices;
	}

	@Override
	public String toString() {
		StringBuilder b = new StringBuilder();
		for (ChannelClass ch : map.keySet()) {
			for (MethodExec exec : map.get(ch)) {
				b.append(ch.getChannel()+" "+ch.getCls().toString()+" "+exec.getObject().toString()+" "+exec.getMethod().getName()+"\n");
			}
		}
		return b.toString();
	}
}
