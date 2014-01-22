package info.kwarc.sally.projects;
/*
import info.kwarc.mmt.api.frontend.Controller;
import info.kwarc.mmt.api.modules.DeclaredTheory;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.vfs2.FileObject;

public class MMTIndexHandler implements IndexHandler, STeXParsingEvents  {
	Controller mmtController;
	DeclaredTheory current = null;
	STexParser parser;
	SallyInteraction interaction;

	public MMTIndexHandler(SallyInteraction interaction) {
		mmtController = new Controller();
		parser = new STexParser();
		this.interaction = interaction;
	}

	public List<String> listAllTheories() {
		List<String> result = new ArrayList<String>();
		for (DeclaredTheory theory : MMTWrapper.getAllTheories(mmtController)) {
			result.add(theory.path().toPath());
		}
		return result;
	}
	
	@Override
	public void symbolDec(String symbolId, int offset) {
		if (current == null) 
			return;
		mmtController.add(MMTWrapper.createConstant(current, symbolId));
	}

	@Override
	public void beginModule(String fileURL, String moduleID, int offset) {
		current = MMTWrapper.createTheory(fileURL, moduleID);
		mmtController.add(current);					
	}

	@Override
	public void importModule(String theory, String symbol, int offset) {
		if (current == null) 
			return;
		mmtController.add(MMTWrapper.createImport(current, MMTWrapper.createTheory(theory, symbol)));
	}
	
	@Override
	public void restart(FileObject root) {
		parser.doIndex(interaction, new TeXSelector(), root);
	}

	@Override
	public void getLog() {
		
	}

	@Override
	public void destroy() {
		
	}

	/*
	@SallyService(channel="/autocomplete")
	public void doQuery(TextAutocomplete query, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		SallyInteraction interaction = context.getCurrentInteraction();

		String fileContents = null;
		if (!query.hasFileContents()) {
			fileContents = interaction.getOneInteraction("/project/getFile", query.getFile().getResourceURI(), String.class);
		} else
			fileContents = query.getFileContents();

		final int queryOffet = query.getOffset();
		final List<String> result = new ArrayList<String>();

		parser.sTeXToMMT(fileContents, parser.removeExtension(query.getFile().getResourceURI()), interaction, new STeXParsingEvents() {

			@Override
			public void symbolDec(String symbolId, int offset) {
			}

			@Override
			public void importModule(String theory, String symbol, int offset) {

			}

			@Override
			public void beginModule(String fileURL, String moduleID, int offset) {
				if (offset < queryOffet) {
					result.clear();
					DeclaredTheory theory = MMTWrapper.createTheory(fileURL, moduleID);
					List<String> constants = MMTWrapper.getConstantsInTheory(mmtController, theory);
					result.addAll(constants);
				}
			}
		});
		for (String constants : result) {
			acceptor.acceptResult(constants);
		} 
	}
	
}

*/
