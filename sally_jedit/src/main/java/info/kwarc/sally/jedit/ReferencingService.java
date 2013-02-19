package info.kwarc.sally.jedit;

import info.kwarc.references.HTMLSectionProvider;
import info.kwarc.references.IReferenceAcceptor;
import info.kwarc.references.LaTeXSectionProvider;
import info.kwarc.references.ReferenceProvider;
import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.FileContents;
import sally.FileRef;
import sally.TextFileNotifications;

public class ReferencingService {

	HashMap<String, List<ReferenceProvider>> providers;
	
	Logger log;
	
	void addNewProvider(String mime, ReferenceProvider provider) {
		if (!providers.containsKey(mime))
			providers.put(mime, new ArrayList<ReferenceProvider>());
		providers.get(mime).add(provider);
	}
	
	public ReferencingService() {
		log = LoggerFactory.getLogger(this.getClass());
		providers = new HashMap<String, List<ReferenceProvider>>();
		addNewProvider("application/stex", new LaTeXSectionProvider());
		addNewProvider("application/xhtml", new HTMLSectionProvider());
	}
	
	@SallyService(channel="/get/semantics")
	public void getSemanticReferences(FileRef f, final SallyActionAcceptor acceptor, SallyContext context) {
		String mime = f.getMime();
		if (!providers.containsKey(mime))
			return;

		SallyInteraction interaction = context.getCurrentInteraction();
		FileContents fileContents = interaction.getOneInteraction("/get", f, FileContents.class);
		if (fileContents == null) {
			log.debug(String.format("Could not get contents of file %s", f.toString()));
			return;
		}

		final TextFileNotifications.Builder result = TextFileNotifications.newBuilder();
		result.setFile(f);
		
		IReferenceAcceptor _acc = new IReferenceAcceptor() {
			public void accept(Object notification) {
				acceptor.acceptResult(notification);
			}
		};
		
		for (ReferenceProvider provider : providers.get(mime)) {
			provider.provide(mime, fileContents.getContents(), _acc);
		}
	}
	
}
