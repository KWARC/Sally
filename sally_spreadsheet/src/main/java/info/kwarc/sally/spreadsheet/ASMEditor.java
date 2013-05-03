package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyMenuItem;
import info.kwarc.sally.core.SallyService;

import javax.ws.rs.GET;
import javax.ws.rs.Path;

import sally.CellPosition;

@Path("/asmeditor")
public class ASMEditor {

	@SallyService
	public void ASMEditService(CellPosition cell, SallyActionAcceptor acceptor, SallyContext context) {
		SallyInteraction sally = context.getCurrentInteraction();

		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Create ontology links") {
			@Override
			public void run() {
			}
		});	
	}

	@GET
	public String editor() {
		return "hi";
	}

}
