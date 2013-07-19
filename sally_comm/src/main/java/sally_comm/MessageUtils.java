package sally_comm;

import sally.WhoAmI;
import sally.WhoAmI.ClientType;
import sally.WhoAmI.DocType;
import sally.WhoAmI.EnvironmentType;

public class MessageUtils {
	public static WhoAmI createDesktopSpreadsheetAlex() {
		return WhoAmI.newBuilder().setClientType(ClientType.Alex).setDocumentType(DocType.Spreadsheet).setEnvironmentType(EnvironmentType.Desktop).build();
	}
}
