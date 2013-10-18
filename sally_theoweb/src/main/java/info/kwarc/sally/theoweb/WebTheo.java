package info.kwarc.sally.theoweb;

import java.util.List;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.theo.Theo;

public class WebTheo implements Theo {

	public SallyMenuItem letUserChoose(List<SallyMenuItem> menuItem) {
		
		return null;
	}

	public int openWindow(Long ProcessInstanceID, String title, String URL,
			int sizeX, int sizeY) {
		return 0;
	}

	public void updateWindow(int windowID, String title, String URL,
			Integer sizeX, Integer sizeY) {
		
	}

	public void closeWindow(int windowID) {
		
	}

}
