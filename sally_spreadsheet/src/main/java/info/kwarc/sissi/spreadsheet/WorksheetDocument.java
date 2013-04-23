package info.kwarc.sissi.spreadsheet;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyMenuItem;
import info.kwarc.sally.core.SallyModelRequest;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sissi.model.document.spreadsheet.ASMInterface;

import java.util.List;

import sally.AlexClick;
import sally.CellPosition;
import sally.IdData;
import sally.MMTUri;
import sally.RangeSelection;
import sally.SpreadsheetModel;
import sally.StringData;

public class WorksheetDocument {
	
	ASMInterface asm;
	String filePath;
	
	public WorksheetDocument(String filePath) {
		asm = new ASMInterface(filePath);
		this.filePath = filePath;
	}
	
	public void setSemanticData(SpreadsheetModel msg) {
		asm.reconstruct(msg);		
	}
	
	public int getSheetId(String sheetName) {
		return asm.getWorksheetIDByName(StringData.newBuilder().setName(sheetName).build()).getId();
	}
	
	/**
	 * Returns the MMT uri corresponding to a clicked position
	 * @param click
	 * @return
	 */
	public String getSemantics(CellPosition click) {
		return asm.getOntologyForPosition(click);
	}

	/**
	 * Heuristic to get a position in the speadsheet matching the MMT uri
	 * @param mmtURI
	 * @return
	 */
	public CellPosition getPositionFromMMTURI(String mmtURI) {
		List<Integer> structs = asm.getListOntologyStructures(mmtURI);
		if (structs.size() == 0)
			return null;
		int structId = structs.get(0);
		RangeSelection sel = asm.getBlockPosition(IdData.newBuilder().setId(structId).build());
		return CellPosition.newBuilder().setSheet(Integer.parseInt(sel.getSheet())).setCol(sel.getStartCol()).setRow(sel.getStartRow()).build();
	}
	
	@SallyService(channel="/get/semantics")
	public void getModel(SallyModelRequest click, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(asm.getRDFModel());
	}
	
	@SallyService(channel="/service/alex/selectRange")
	public void alexClickInteraction(AlexClick click, SallyActionAcceptor acceptor, SallyContext context) {
		if (!click.getFileName().equals(filePath))
			return;
		final SallyInteraction interaction = context.getCurrentInteraction();

		context.setContextVar("preferred_position", click.getPosition());
		
		int sheet = getSheetId(click.getSheet());
		RangeSelection sel = click.getRange();
		
		CellPosition pos = CellPosition.newBuilder().setSheet(sheet).setRow(sel.getStartRow()).setCol(sel.getStartCol()).build();
		
		MMTUri mmtURI = interaction.getOneInteraction(pos, MMTUri.class);
		List<SallyMenuItem> items = interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class);
		SallyMenuItem item = interaction.getOneInteraction(items, SallyMenuItem.class);
		if (item != null) {
			item.run();
		}
	}
	
	@SallyService
	public void getPositionFromMMTURI(MMTUri uri, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(getPositionFromMMTURI(uri.getUri()));
	}
	
	@SallyService
	public void getSemantics(CellPosition click, SallyActionAcceptor acceptor, SallyContext context) {
		String uri = getSemantics(click);
		if (uri != null)
			acceptor.acceptResult(MMTUri.newBuilder().setUri(uri).build());
	}
	
}
