package info.kwarc.sally.spreadsheet.interfaces;

import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import sally.SpreadsheetAlexData;

public interface WorksheetFactory {
	public SpreadsheetDocument create(String filePath, SpreadsheetAlexData data, INetworkSender sender);
}
