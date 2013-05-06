package info.kwarc.sally.core;

import java.util.HashMap;
import java.util.Random;

public class SallyContextManager {
	HashMap<String, SallyContext> contexts;
	Random rand;
	
	private static SallyContextManager instance = null;

	static public SallyContextManager getInstance() {
		if (instance == null) {
			instance = new SallyContextManager();
		}
		return instance;
	}
	
	public SallyContextManager() {
		rand = new Random();
		contexts = new HashMap<String, SallyContext>();
	}
	
	public SallyContext getContext(String id) {
		if (id == null)
			return null;
		return contexts.get(id);
	}
	
	public SallyContext getEmptyContext(SallyInteraction interaction) {
		SallyContextImpl result = new SallyContextImpl();
		result.setInteraction(interaction);
		String token = Long.toString(rand.nextLong());
		result.setToken(token);
		
		contexts.put(token, result);
		return result;
	}
}
