package info.kwarc.sally.core.comm;


public abstract class SallyMenuItem implements Runnable {

	String frame, service, explanation;
	
	public String getFrame() {
		return frame;
	}
	
	public String getService() {
		return service;
	}
	
	public String getExplanation() {
		return explanation;
	}
	
	public SallyMenuItem(String frame, String service, String explanation) {
		this.frame = frame;
		this.service = service;
		this.explanation = explanation;
	}	
}