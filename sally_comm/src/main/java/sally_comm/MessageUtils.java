package sally_comm;

import sally.DocType;
import sally.WhoAmI;
import sally.WhoAmI.ClientType;
import sally.WhoAmI.EnvironmentType;

public class MessageUtils {
	public static WhoAmI createDesktopSpreadsheetAlex() {
		return WhoAmI.newBuilder().setClientType(ClientType.Alex).setDocumentType(DocType.Spreadsheet).setEnvironmentType(EnvironmentType.Desktop).build();
	}

	public static WhoAmI createDesktopCADAlex() {
		return WhoAmI.newBuilder().setClientType(ClientType.Alex).setDocumentType(DocType.CAD).setEnvironmentType(EnvironmentType.Desktop).build();
	}

}
