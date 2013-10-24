package info.kwarc.sally.html;

import info.kwarc.sally.core.net.INetworkSender;
import sally.HTMLASM;


public interface HTMLFactory {
	public HTMLDocument create(String filePath, HTMLASM data, INetworkSender networkSender);
}
