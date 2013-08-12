package info.kwarc.sally.spreadsheet.interfaces;

import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import sally.SpreadsheetModel;

public interface WorksheetFactory {
	public WorksheetDocument create(String filePath, SpreadsheetModel data, INetworkSender sender);
}
