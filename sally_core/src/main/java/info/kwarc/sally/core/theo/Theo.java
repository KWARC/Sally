package info.kwarc.sally.core.theo;

import info.kwarc.sally.core.doc.DocumentInformation;

public interface Theo {
	int openWindow(DocumentInformation sender, Long requestWorkflowID, String title, String URL, int sizeX, int sizeY);
	void updateWindow(DocumentInformation sender, int windowID, String title, String URL, Integer sizeX, Integer sizeY);
	void closeWindow(DocumentInformation sender, int windowID);

}
