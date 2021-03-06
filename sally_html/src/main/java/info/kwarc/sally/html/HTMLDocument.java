package info.kwarc.sally.html;

import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.interaction.SallyMenuItem;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.rdf.IM;
import info.kwarc.sally.core.rdf.RDFStore;
import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.IPositionProvider;
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
	HashMap<String, String> urimap;
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
		urimap = new HashMap<String, String>();
		init();
	}
	
	public void selectObject(String id) {
		HTMLSelectPart selCmd = HTMLSelectPart.newBuilder().setId(id).setFileName(filePath).build();
		sender.sendMessage("/html/htmlSelectPart", selCmd);
	}
	
	@SallyService(channel="navigateTo")
	public void navigateTo(final SoftwareObject so, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		if (!filePath.equals(so.getFileName()))
			return;
		acceptor.acceptResult(new Runnable() {
			
			@Override
			public void run() {
				selectObject(so.getUri().substring(7));
			}
		});
	}

	@SallyService	
	public void sketchClickInteraction(final MMTUri mmtURI, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		final Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);
		String origFile = context.getContextVar("origFile", String.class);
		if (filePath.equals(origFile))
			return;
		final List<String> refs = new ArrayList<String>();
		for (String key : urimap.keySet()) {
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
					Long callbackid = callbacks.registerCallback(new IMessageCallback() {
						
						@Override
						public void onMessage(AbstractMessage m) {
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
		for (String key : urimap.keySet()) {
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

	public String getSemantics(String id) {
		return urimap.get(id);
	}

}
