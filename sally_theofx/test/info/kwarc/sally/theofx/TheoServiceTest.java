/*package info.kwarc.sally.theofx.communicator;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.theofx.ui.TheoWindow;

public class TheoServiceTest {
	
	
	
	public static void main(String[] args) {
		SallyInteraction sallyInteract = new SallyInteraction();
		CometD cometD = new CometD(8080);
		cometD.start();
		cometD.channelToInteraction(sallyInteract);
		
		sallyInteract.registerServices(new TheoService());
		sallyInteract.registerServices(cometD);

		//TheoWindow.addCommunicationWindow(sallyInteract);
		TheoWindow.addWindow(1, 200, 200, 200, 200, "bla", "http://localhost:8080/sally/index.html", null, true);
	
	}
}














//TheoWindow.addCommunicationWindow();*/