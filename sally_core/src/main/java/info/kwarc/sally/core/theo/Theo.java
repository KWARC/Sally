package info.kwarc.sally.core.theo;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.comm.SallyMenuItem;

import java.util.List;

public interface Theo {
	void letUserChoose(DocumentInformation sender, List<SallyMenuItem> menuItem);
	int openWindow(DocumentInformation sender, Long requestWorkflowID, String title, String URL, int sizeX, int sizeY);
	void updateWindow(DocumentInformation sender, int windowID, String title, String URL, Integer sizeX, Integer sizeY);
	void closeWindow(DocumentInformation sender, int windowID);

}
