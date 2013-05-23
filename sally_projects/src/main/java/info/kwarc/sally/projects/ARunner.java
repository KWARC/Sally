package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.theofx.TheoService;


public class ARunner {

	public static void main(String[] args) {
		SallyInteraction interaction = new SallyInteraction();
		CometD cometd = new CometD(8080);
		cometd.start();
		cometd.channelToInteraction(interaction);

		Project serv = new Project("/home/costea/kwarc/stc");

		serv.addIndexer(new MMTIndexHandler());
		
		PathAliasManager alias = new PathAliasManager();
		alias.addPrefix("SiSsI", "file:///home/costea/kwarc/stc/sissi");
		//		alias.addPrefix("KWARCslides", "file:///home/costea/kwarc/stc/slides");


		interaction.registerServices(cometd);
		interaction.registerServices(serv);
		interaction.registerServices(new TheoService());
		interaction.registerServices(alias);

/*
		mmt.doIndex(interaction, new TeXSelector());
		FileRef f = FileRef.newBuilder().setMime("text/stex").setResourceURI("file:///home/costea/kwarc/stc/sissi/winograd/cds/admincosts.tex").build();

		TextAutocomplete auto = TextAutocomplete.newBuilder().setFile(f).setOffset(159).build();
		List<String> results = interaction.getPossibleInteractions("/autocomplete", auto, String.class);
		for (String s : results)
			System.out.println(s);*/
	}
}