package info.kwarc.sally.core.comm;

import info.kwarc.sally.core.interfaces.IAbstractMessageRunner;

import java.util.HashMap;
import java.util.Random;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class CallbackManager {
	
	Random rand;
	HashMap<Long, IAbstractMessageRunner> callbacks;
	
	@Inject
	public CallbackManager() {
		rand = new Random();
		callbacks  = new HashMap<Long, IAbstractMessageRunner>();
	}
	
	public Long registerCallback(IAbstractMessageRunner abs) {
		long newID = rand.nextLong();
		callbacks.put(newID, abs);
		return newID;
	}
	
	public IAbstractMessageRunner getCallback(Long l) {
		return callbacks.get(l);
	}
}
