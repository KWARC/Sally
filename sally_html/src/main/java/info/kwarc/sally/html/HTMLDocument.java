package info.kwarc.sally.html;

import info.kwarc.sally.core.RDFStore;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.IPositionProvider;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.ontologies.IM;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.html.ontology.HTML;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.HTMLASM;
import sally.HTMLAtomic;
import sally.HTMLSelect;
import sally.HTMLSelectPart;
import sally.MMTUri;
import sally.ScreenCoordinates;
import sally.SketchSelectPart;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;

public class HTMLDocument {
	String filePath;
	HTMLASM data;
	INetworkSender sender;
	HashMap<Integer, String> urimap;
	IPositionProvider provider;
	Logger log;
	RDFStore rdfStore;

	@Inject
	public HTMLDocument(@Assisted String filePath, @Assisted HTMLASM data, @Assisted INetworkSender sender,  IPositionProvider provider, RDFStore rdfStore) {
		this.filePath = filePath;
		this.data = data;
		this.sender = sender;
		this.provider = provider;
		this.rdfStore = rdfStore;
		log = LoggerFactory.getLogger(getClass());
		urimap = new HashMap<Integer, String>();
		init();
	}

	@SallyService	
	public void sketchClickInteraction(MMTUri mmtURI, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		String origFile = context.getContextVar("origFile", String.class);
		if (filePath.equals(origFile))
			return;
		final List<Integer> refs = new ArrayList<Integer>();
		for (int key : urimap.keySet()) {
			if (urimap.get(key).equals(mmtURI.getUri())) {
				refs.add(key);
			}
		}
		if (refs.size() == 0)
			return;

		if (refs.size() == 1) {
			acceptor.acceptResult(new SallyMenuItem("References", "In "+filePath, "Show references in text") {
				@Override
				public void run() {
					HTMLSelectPart selCmd = HTMLSelectPart.newBuilder().setId(refs.get(0)).setFileName(filePath).build();
					sender.sendMessage("/html/htmlSelectPart", selCmd);
				}
			});
		} else {
			acceptor.acceptResult(new SallyMenuItem("References", "In "+filePath+" ("+refs.size()+")", "Show references in text") {
				@Override
				public void run() {
					SketchSelectPart selCmd = SketchSelectPart.newBuilder().setId(refs.get(0)).setFileName(filePath).build();
					sender.sendMessage("/html/htmlSelectPart", selCmd);
				}
			});
		}
	}


	void init() {
		for (HTMLAtomic sa : data.getPartsList()) {
			urimap.put(sa.getId(), sa.getMmturi().getUri());
		}
		rdfStore.addModel(filePath, createModel());
	}

	private Model createModel() {
		Model model = ModelFactory.createDefaultModel();
		model.setNsPrefix("rdf", RDF.getURI());
		for (Integer key : urimap.keySet()) {
			Resource comp = model.createResource();
			model.add(comp, IM.partOfFile, model.createLiteral(filePath));
			model.add(comp, IM.ontologyURI, model.createLiteral(urimap.get(key)));
			model.add(comp, HTML.hasHTMLID, model.createTypedLiteral(key));
		}
		return model;
	}

	@SallyService
	public void htmlClickInteraction(HTMLSelect click, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		context.setContextVar("origFile", filePath);
		if (!click.getFileName().equals(filePath)) {
			return;
		}
		final SallyInteraction interaction = context.getCurrentInteraction();

		ScreenCoordinates coords = click.getPosition();
		provider.setRecommendedCoordinates(new Coordinates(coords.getX(), coords.getY()));

		MMTUri mmtURI = MMTUri.newBuilder().setUri(getSemantics(click.getId())).build();
		if (mmtURI == null)
			return;

		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();
		items.addAll(interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class));
		for (SallyMenuItem r : items) {
			acceptor.acceptResult(r);
		}
	}

	public String getSemantics(int id) {
		return urimap.get(id);
	}

}
