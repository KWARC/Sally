package info.kwarc.sally.sketch;

import info.kwarc.sally.core.net.INetworkSender;
import Sally.SketchASM;


public interface SketchFactory {
	public SketchDocument create(String filePath, SketchASM data, INetworkSender networkSender);
}
