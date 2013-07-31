package info.kwarc.sally.core.interfaces;

import info.kwarc.sally.core.comm.SallyMenuItem;

import java.util.List;

public interface Theo {
	SallyMenuItem letUserChoose(List<SallyMenuItem> menuItem);
	int openWindow(String title, String URL, int sizeX, int sizeY);
}
