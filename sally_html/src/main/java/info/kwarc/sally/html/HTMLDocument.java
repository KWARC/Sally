package info.kwarc.sally.html;

import info.kwarc.sally.core.RDFStore;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.interfaces.IAbstractMessageRunner;
import info.kwarc.sally.core.interfaces.IPositionProvider;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.ontologies.IM;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.html.ontology.HTML;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.drools.runtime.process.ProcessInstance;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.HTMLASM;
import sally.HTMLAtomic;
import sally.HTMLSelect;
import sally.HTMLSelectPart;
import sally.MMTUri;
import sally.ScreenCoordinates;
import sally.SoftwareObject;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.protobuf.AbstractMessage;
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
	ISallyWorkflowManager wm;
	CallbackManager callbacks;
	
	@Inject
	public HTMLDocument(@Assisted String filePath, @Assisted HTMLASM data, @Assisted INetworkSender sender,  IPositionProvider provider, RDFStore rdfStore, ISallyWorkflowManager wm, CallbackManager callbacks) {
		this.filePath = filePath;
		this.callbacks = callbacks;
		this.wm = wm;
		this.data = data;
		this.sender = sender;
		this.provider = provider;
		this.rdfStore = rdfStore;
		log = LoggerFactory.getLogger(getClass());
		urimap = new HashMap<Integer, String>();
		init();
	}
	
	public void selectObject(int id) {
		HTMLSelectPart selCmd = HTMLSelectPart.newBuilder().setId(id).setFileName(filePath).build();
		sender.sendMessage("/html/htmlSelectPart", selCmd);
	}

	@SallyService	
	public void sketchClickInteraction(final MMTUri mmtURI, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		final Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);
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
			acceptor.acceptResult(new SallyMenuItem("Go to", "In "+filePath, "Show references in text") {
				@Override
				public void run() {
					selectObject(refs.get(0));
				}
			});
		} else {
			acceptor.acceptResult(new SallyMenuItem("Go to", "In "+filePath+" ("+refs.size()+")", "Show references in text") {
				@Override
				public void run() {
					Long callbackid = callbacks.registerCallback(new IAbstractMessageRunner() {
						
						@Override
						public void run(AbstractMessage m) {
							selectObject(((HTMLSelectPart)m).getId());
						}
					});
					
					HashMap<String, Object>  input = new  HashMap<String, Object>();
					
					input.put("ObjectIDs", refs);
					input.put("CallbackID", Long.toString(callbackid));
					ProcessInstance pi =wm.prepareProcess(parentProcessInstanceID, "Sally.sketch_navigation", input);
					HandlerUtils.setProcessVariable(pi, "ServiceURL", "http://localhost:8181/sally/html/navigate?id="+pi.getId());
					wm.startProcess(pi);					
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

		List<SallyMenuItem> items = new ArrayList<SallyMenuItem>();

		SoftwareObject obj = SoftwareObject.newBuilder().setFileName(filePath).setUri("htmlid#"+click.getId()).build();
		items.addAll(interaction.getPossibleInteractions(obj, SallyMenuItem.class));
		
		MMTUri mmtURI = MMTUri.newBuilder().setUri(getSemantics(click.getId())).build();
		if (mmtURI != null)
			items.addAll(interaction.getPossibleInteractions(mmtURI, SallyMenuItem.class));
		
		
		for (SallyMenuItem r : items) {
			acceptor.acceptResult(r);
		}
	}

	public String getSemantics(int id) {
		return urimap.get(id);
	}

}
