package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyInteraction;


public class ARunner {

	public static void main(String[] args) {
		ProjectService serv = new ProjectService("/home/costea/kwarc/stc/sissi");
		MMTService mmt = new MMTService();
		//BaseXService baseX = new BaseXService("localhost", 1984, "admin", "admin");
		SallyInteraction interaction = new SallyInteraction();
		interaction.registerServices(serv);
		interaction.registerServices(mmt);
		//interaction.registerServices(baseX);

		mmt.doIndex(interaction, new TeXSelector());
		//List<String> results = interaction.getPossibleInteractions("/queryXML", "xquery doc('database')", String.class);
	}
}