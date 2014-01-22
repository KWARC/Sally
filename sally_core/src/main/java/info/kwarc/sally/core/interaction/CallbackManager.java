package info.kwarc.sally.core.interaction;

import java.util.HashMap;
import java.util.Random;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class CallbackManager {
	
	Random rand;
	HashMap<Long, IMessageCallback> callbacks;
	
	@Inject
	public CallbackManager() {
		rand = new Random();
		callbacks  = new HashMap<Long, IMessageCallback>();
	}
	
	public Long registerCallback(IMessageCallback abs) {
		long newID = rand.nextLong();
		callbacks.put(newID, abs);
		return newID;
	}
	
	public IMessageCallback getCallback(Long l) {
		return callbacks.get(l);
	}
}
