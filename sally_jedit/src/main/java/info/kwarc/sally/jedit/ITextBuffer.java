package info.kwarc.sally.jedit;


public interface ITextBuffer {
	String getPath();
	
	String getText();
	void addMarker(int line, String text);
	void addOnChangeListener(Runnable runnable);
	
	void removeAllMarkers();
}
