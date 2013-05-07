package info.kwarc.sally.theoxul;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;

import java.io.IOException;

import sally.ScreenCoordinates;
import sally.TheoOpenWindow;

public class TheoTest {
	public static void main(String[] args) throws IOException {
		String xulPath = "/opt/xulrunner/xulrunner";
		String xulApp = "/home/costea/kwarc/sissi/trunk/xultheo3/application.ini";
		SallyInteraction interaction = new SallyInteraction();
		CometD cometd = new CometD(8080);
		cometd.start();
		cometd.channelToInteraction(interaction);
		
		interaction.registerServices(cometd);
		interaction.registerServices(new TheoService(xulPath, xulApp));

		TheoOpenWindow window = TheoOpenWindow.newBuilder()
				.setPosition(ScreenCoordinates.newBuilder().setX(100).setY(100).build())
				.setSizeX(300).setSizeY(100).setCookie("").setTitle("Create Link to Ontology")
				.setUrl("http://localhost:8080/asmeditor").build();

		interaction.getOneInteraction(window, Boolean.class);
	}
}
