package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.rdf.RDFStore;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.IPositionProvider;
import info.kwarc.sally.sharejs.IDocManager;
import info.kwarc.sally.sharejs.JSONSnapshot;
import info.kwarc.sally.sharejs.models.SpreadsheetModel;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.export.ModelRDFExport;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexClick;
import sally.AlexRangeRequest;
import sally.MMTUri;
import sally.RangeSelection;
import sally.ScreenCoordinates;
import sally.SpreadsheetAlexData;
import sally.SwitchToApp;

import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.inject.name.Named;
import com.google.protobuf.AbstractMessage;

public class SpreadsheetDocument {

	INetworkSender sender;

	Manager asm;
	Logger log;

	RDFStore rdfStore;
	
	String filePath;
	IPositionProvider provider;
	SpreadsheetModel shareJSModel;

	IOntologyProvider ontoProvider;
	IDocManager documentManager;

	public String getFilePath() {
		return filePath;
	}

	@Inject
	public SpreadsheetDocument(@Assisted String filePath, @Assisted SpreadsheetAlexData data, @Assisted INetworkSender sender, IPositionProvider provider, IDocManager documentManager, @Named("ShareJSCollection") String shareJSCollection, RDFStore rdfStore) {
		asm = new Manager(ontoProvider, data.getAsm());
		this.filePath = filePath;
		this.sender = sender;
		this.provider = provider;
		this.rdfStore = rdfStore;
		log = LoggerFactory.getLogger(getClass());
		
		ObjectMapper mapper = new ObjectMapper(); // create once, reuse
		try {
			JSONSnapshot snap  = JSONSnapshot.retrieveSnapshot(documentManager, shareJSCollection, filePath);
			if (snap.getSnapshot() != null)
				shareJSModel= mapper.readValue(snap.getSnapshot(), SpreadsheetModel.class);
		} catch (JsonParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (JsonMappingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		rdfStore.addModel(filePath, ModelRDFExport.getRDF(asm, filePath));
	}

	public SpreadsheetModel getConcreteSpreadsheetModel() {
		return shareJSModel;
	}

	public void switchToApp() {
		SwitchToApp request = SwitchToApp.newBuilder().setFileName(filePath).build();
		sender.sendMessage("/do/switch", request, new IMessageCallback() {

			@Override
			public void onMessage(AbstractMessage msg) {

			}
		});
	}

	public Block createBlock(String sheet, int startRow, int startCol, int endRow, int endCol) {
		List<CellSpaceInformation> blockPositions = Util.expandRange(
				new CellSpaceInformation(sheet, startRow, startCol), new CellSpaceInformation(sheet, endRow, endCol));
		return asm.createComposedBlock(blockPositions);
	}

	public Manager getASMModel() {
		return asm;
	}

	public void selectRange(String sheet, int startRow, int endRow, int startCol, int endCol) {
		RangeSelection sel = RangeSelection.newBuilder().setSheet(sheet).setStartRow(startRow).setEndRow(endRow).setStartCol(startCol).setEndCol(endCol).build();
		AlexRangeRequest request = AlexRangeRequest.newBuilder().setFileName(filePath).addSelection(sel).build();
		selectRange(request);
	}

	public void selectRange(AlexRangeRequest request) {
		sender.sendMessage("/do/select", request, new IMessageCallback() {
			@Override
			public void onMessage(AbstractMessage msg) {

			}
		});
	}	


	public void getData(String sheet, int startRow, int endRow, int startCol, int endCol) {
		RangeSelection sel = RangeSelection.newBuilder().setSheet(sheet).setStartRow(startRow).setEndRow(endRow).setStartCol(startCol).setEndCol(endCol).build();
		AlexRangeRequest request = AlexRangeRequest.newBuilder().setFileName(filePath).addSelection(sel).build();
		sender.sendMessage("/get/data", request, new IMessageCallback() {

			@Override
			public void onMessage(AbstractMessage msg) {

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
		String uri = getSemantics(sel);
		if (uri == null)
			return;
		MMTUri mmtURI = MMTUri.newBuilder().setUri(uri).build();

		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();
		items.addAll(interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class));
		for (SallyMenuItem r : items) {
			acceptor.acceptResult(r);
		}
	}


	@SallyService
	public void getPositionFromMMTURI(MMTUri uri, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(getPositionFromMMTURI(uri.getUri()));
	}
}
