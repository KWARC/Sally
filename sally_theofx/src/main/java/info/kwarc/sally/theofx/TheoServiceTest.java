package info.kwarc.sally.theofx;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.theofx.ui.TheoWindow;
import info.kwarc.sally.theofx.windowManager.WindowActions;

import java.util.ArrayList;
import java.util.List;

import sally.Cookie;

public class TheoServiceTest {



	public static void main(String[] args) {
		/*		SallyInteraction sallyInteract = new SallyInteraction();
		CometD cometD = new CometD(8080);
		cometD.start();
		cometD.channelToInteraction(sallyInteract);

		sallyInteract.registerServices(new TheoService());
		sallyInteract.registerServices(cometD);

		//TheoWindow.addCommunicationWindow(sallyInteract);
		TheoWindow.addWindow(sallyInteract, 200, 200, 200, 200, "bla", "http://localhost:8080/sally/index.html", null, true);
		 */
		System.getProperties().list(System.out);
		WindowActions.bringToFront("excel", "newContractMarineEngineCoolingSystem.ods");
/*		TheoService service = new TheoService(null, null, null);
		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();

		items.add(new SallyMenuItem("Knowledge Base", "Definition Lookup", "Here comes some description") {
			@Override
			public void run() {
				// TODO Auto-generated method stub

			}
		});
		items.add(new SallyMenuItem("Knowledge Base", "Semantic Navigation", "Here comes some description") {
			@Override
			public void run() {
				// TODO Auto-generated method stub

			}
		});
		items.add(new SallyMenuItem("Pricing", "Price", "Here comes some description") {
			@Override
			public void run() {
				// TODO Auto-generated method stub

			}
		});
		service.letUserChoose(items);*/
		
		//TheoWindow.addWindow(1, 200, 200, 200, 200, "Sally Instance Selector", "http://localhost:8080/sally/index.html", null, true);
	}
}














//TheoWindow.addCommunicationWindow();