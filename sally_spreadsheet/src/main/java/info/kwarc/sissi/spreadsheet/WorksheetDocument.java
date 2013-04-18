package info.kwarc.sissi.spreadsheet;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sissi.model.document.spreadsheet.ASMInterface;

import java.util.List;

import sally.CellPosition;
import sally.IdData;
import sally.MMTUri;
import sally.RangeSelection;
import sally.SpreadsheetModel;
import sally.StringData;

public class WorksheetDocument {
	
	ASMInterface asm;
	
	public WorksheetDocument(String filePath) {
		asm = new ASMInterface(filePath);
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
	
	@SallyService
	public void getPositionFromMMTURI(MMTUri uri, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(getPositionFromMMTURI(uri.getUri()));
	}
	
	@SallyService
	public void getSemantics(CellPosition click, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(MMTUri.newBuilder().setUri(getSemantics(click)).build());
	}
	
}
