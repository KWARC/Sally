package info.kwarc.sally.theofx.windowManager;

public class OSDiagnostics {
	
	String Name;
	String Desktop;
	String Version;
	String Architecture;
	
	public OSDiagnostics() {
		this.Name = System.getProperty("os.name");
		this.Desktop = System.getProperty("sun.desktop");
		this.Version = System.getProperty("os.version");
		this.Architecture = System.getProperty("os.arch");
	}
	
}
