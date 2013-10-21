package info.kwarc.sally.core.theo;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.net.INetworkSender;

import java.util.List;

public interface Theo {
	void letUserChoose(INetworkSender sender, Long ProcessInstanceID, List<SallyMenuItem> menuItem);
	int openWindow(INetworkSender sender, Long ProcessInstanceID, String title, String URL, int sizeX, int sizeY);
	void updateWindow(INetworkSender sender, int windowID, String title, String URL, Integer sizeX, Integer sizeY);
	void closeWindow(INetworkSender sender, int windowID);

}
