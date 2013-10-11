package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.Coordinates;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.comm.SallyModelRequest;
import info.kwarc.sally.core.interfaces.IPositionProvider;
import info.kwarc.sally.core.interfaces.Theo;
import info.kwarc.sally.networking.interfaces.IMessageCallback;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.spreadsheet3.export.ModelRDFExport;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

import java.util.ArrayList;
import java.util.List;

import sally.AlexClick;
import sally.AlexRangeRequest;
import sally.MMTUri;
import sally.RangeSelection;
import sally.ScreenCoordinates;
import sally.SpreadsheetAlexData;
import sally.SwitchToApp;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

public class WorksheetDocument {

	INetworkSender sender;

	Manager asm;

	String filePath;
	Theo theo;
	IPositionProvider provider;

	IOntologyProvider ontoProvider;

	public String getFilePath() {
		return filePath;
	}

	@Inject
	public WorksheetDocument(@Assisted String filePath, @Assisted SpreadsheetAlexData data, @Assisted INetworkSender sender, IPositionProvider provider) {
		asm = new Manager(ontoProvider, data.getAsm());
		this.filePath = filePath;
		this.sender = sender;
		this.provider = provider;
	}

	public void switchToApp() {
		SwitchToApp request = SwitchToApp.newBuilder().setFileName(filePath).build();
		sender.sendMessage("/do/switch", request, new IMessageCallback() {

			@Override
			public void onMessage() {

			}
		});
	}

	public void selectRange(String sheet, int startRow, int endRow, int startCol, int endCol) {
		RangeSelection sel = RangeSelection.newBuilder().setSheet(sheet).setStartRow(startRow).setEndRow(endRow).setStartCol(startCol).setEndCol(endCol).build();
		AlexRangeRequest request = AlexRangeRequest.newBuilder().setFileName(filePath).addSelection(sel).build();
		selectRange(request);
	}

	public void selectRange(AlexRangeRequest request) {
		sender.sendMessage("/do/select", request, new IMessageCallback() {
			@Override
			public void onMessage() {

			}
		});
	}	


	public void getData(String sheet, int startRow, int endRow, int startCol, int endCol) {
		RangeSelection sel = RangeSelection.newBuilder().setSheet(sheet).setStartRow(startRow).setEndRow(endRow).setStartCol(startCol).setEndCol(endCol).build();
		AlexRangeRequest request = AlexRangeRequest.newBuilder().setFileName(filePath).addSelection(sel).build();
		sender.sendMessage("/get/data", request, new IMessageCallback() {

			@Override
			public void onMessage() {

			}
		});
	}

	public String getSemantics(String sheet, int row, int col) {
		CellSpaceInformation pos = new CellSpaceInformation(sheet, row, col);
		List<Relation> relations = asm.getRelationForPosition(pos);
		if (relations.size() == 0)
			return null;
		return relations.get(0).getUri();
	}

	/**
	 * Returns the MMT uri corresponding to a clicked position
	 * @param click
	 * @return
	 */
	public String getSemantics(RangeSelection click) {
		return getSemantics(click.getSheet(), click.getStartRow(), click.getStartCol());
	}

	/**
	 * Heuristic to get a position in the speadsheet matching the MMT uri
	 * @param mmtURI
	 * @return
	 */
	public CellSpaceInformation getPositionFromMMTURI(String mmtURI) {
		// TODO: NOT IMPLEMENTED
		return null;
	}

	@SallyService
	public void alexClickInteraction(AlexClick click, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		if (!click.getFileName().equals(filePath)) {
			return;
		}
		final SallyInteraction interaction = context.getCurrentInteraction();

		ScreenCoordinates coords = click.getPosition();
		provider.setRecommendedCoordinates(new Coordinates(coords.getX(), coords.getY()));

		RangeSelection sel = click.getRange();
		MMTUri mmtURI = interaction.getOneInteraction(getSemantics(sel), MMTUri.class);
		
		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();
		items.addAll(interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class));
		for (SallyMenuItem r : items) {
			acceptor.acceptResult(r);
		}
	}

	@SallyService(channel="/get/semantics")
	public void getModel(SallyModelRequest click, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(ModelRDFExport.getRDF(asm, filePath));
	}


	@SallyService
	public void getPositionFromMMTURI(MMTUri uri, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(getPositionFromMMTURI(uri.getUri()));
	}
}
