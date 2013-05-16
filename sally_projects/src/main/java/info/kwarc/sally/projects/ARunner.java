package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyInteraction;

import java.util.List;


public class ARunner {

	public static void main(String[] args) {
		ProjectService serv = new ProjectService("/home/costea/kwarc/stc/sissi");
		BaseXService baseX = new BaseXService("localhost", 1984, "admin", "admin");
		SallyInteraction interaction = new SallyInteraction();
		interaction.registerServices(serv);
		interaction.registerServices(baseX);

		baseX.doIndex(interaction, new OMDocSelector());
		List<String> results = interaction.getPossibleInteractions("/queryXML", "xquery doc('database')", String.class);
	}
}