package info.kwarc.sally.spreadsheet.interfaces;

import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import sally.SpreadsheetAlexData;

public interface WorksheetFactory {
	public WorksheetDocument create(String filePath, SpreadsheetAlexData data, INetworkSender sender);
}
