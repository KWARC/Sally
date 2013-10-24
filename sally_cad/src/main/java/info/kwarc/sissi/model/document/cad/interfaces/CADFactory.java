package info.kwarc.sissi.model.document.cad.interfaces;

import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sissi.model.document.cad.CADDocument;
import sally.CADSemanticData;

public interface CADFactory {
	public CADDocument create(String filePath, CADSemanticData data, INetworkSender sender);
}
