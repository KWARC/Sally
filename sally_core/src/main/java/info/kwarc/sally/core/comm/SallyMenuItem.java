package info.kwarc.sally.core.comm;


public abstract class SallyMenuItem implements Runnable {

	String frame, service;
	
	public String getFrame() {
		return frame;
	}
	
	public String getService() {
		return service;
	}
	
	public SallyMenuItem(String frame, String service) {
		this.frame = frame;
		this.service = service;
	}	
}