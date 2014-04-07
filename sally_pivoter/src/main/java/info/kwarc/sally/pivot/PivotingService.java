package info.kwarc.sally.pivot;

import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.interaction.IMessageCallback;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.core.workflow.ProcessInstance;
import info.kwarc.sally.pivot.ontology.Pivot;

import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.commons.io.IOUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.HTMLSelectPart;
import Sally.SoftwareObject;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.google.protobuf.AbstractMessage;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.vocabulary.RDF;

@Singleton
public class PivotingService {

	SoftwareObject mainObject;
	String getKnowledgeUnitsSparql;
	String getSoftwareObjectSparql;
	String getObjectImplementations;
	String getObjectRequirements;
	Model model;
	DocumentManager docManager;
	CallbackManager callbacks;
	ISallyWorkflowManager wm;
	Logger log;

	@Inject
	public PivotingService(DocumentManager docManager, CallbackManager callbacks, ISallyWorkflowManager wm) {
		model = ModelFactory.createDefaultModel();
		model.setNsPrefix("pivot", Pivot.getURI());
		this.docManager = docManager;
		this.callbacks = callbacks;
		this.wm = wm;
		getKnowledgeUnitsSparql = loadSparql("/getKnowledgeUnits.sparql");
		getSoftwareObjectSparql = loadSparql("/getSoftwareObject.sparql");
		getObjectImplementations = loadSparql("/getObjectImplementations.sparql");
		getObjectRequirements = loadSparql("/getObjectRequirements.sparql");
		log = LoggerFactory.getLogger(getClass());
		readFile();
	}

	void readFile() {
		try {
			model.read("pivot.rdf");
		} catch (Exception e) {

		}
	}

	void saveFile() {
		try {
			model.write(new FileWriter("pivot.rdf"));
		} catch (Exception e) {

		}
	}

	public List<String> getKnowledgeUnits() {
		List<String> result = new ArrayList<String>();

		Query query = QueryFactory.create(getKnowledgeUnitsSparql);
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet resultSet = qe.execSelect();

		while (resultSet.hasNext()) {
			QuerySolution sol = resultSet.next();
			result.add(sol.getLiteral("y").getString());
		}

		return result;
	}

	public void createKnowledgeUnit(String name) {
		Resource newKU = model.createResource();
		model.add(newKU, RDF.type, Pivot.knowledgeUnit);
		model.add(newKU, Pivot.hasName, name);
		saveFile();
	}

	public Resource getKnowledgeUnit(String name) {
		Query query = QueryFactory.create(getKnowledgeUnitsSparql);
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet resultSet = qe.execSelect();

		while (resultSet.hasNext()) {
			QuerySolution sol = resultSet.next();
			if (sol.getLiteral("y").getString().equals(name)) {
				return sol.getResource("x");
			}
		}
		return null;
	}

	public Resource getSoftwareObject(String KU, SoftwareObject so) {
		Query query = QueryFactory.create(String.format(getSoftwareObjectSparql, KU, so.getUri(), so.getFileName()));
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet resultSet = qe.execSelect();

		while (resultSet.hasNext()) {
			QuerySolution sol = resultSet.next();
			return sol.getResource("so");
		}
		return null;
	}

	public Resource addSoftwareObjectToKU(String KU, SoftwareObject so) {
		Resource softObj = getSoftwareObject(KU, so);
		if (softObj != null)
			return softObj;
		Resource soRes = model.createResource();
		model.add(soRes, RDF.type, Pivot.softwareObject);
		model.add(soRes, Pivot.partOfKnowledgeUnit, getKnowledgeUnit(KU));
		model.add(soRes, Pivot.partOfFile, so.getFileName());
		model.add(soRes, Pivot.hasURI, so.getUri());
		saveFile();
		return soRes;
	}


	private HashMap<String, List<String>> getObjectReferences(SoftwareObject so, String sparqlQuery) {
		HashMap<String, List<String>> result  = new HashMap<String, List<String>>();

		Query query = QueryFactory.create(String.format(sparqlQuery, so.getUri(), so.getFileName()));
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet resultSet = qe.execSelect();

		while (resultSet.hasNext()) {
			QuerySolution sol = resultSet.next();
			String soFile = sol.getLiteral("realFile").getString();
			String soURI = sol.getLiteral("realURI").getString();
			if (!result.containsKey(soFile))
				result.put(soFile, new ArrayList<String>());
			result.get(soFile).add(soURI);
		}
		return result;
	}

	void navigateTo(SallyInteraction interact, String fileName, String URI) {
		SoftwareObject obj = SoftwareObject.newBuilder().setFileName(fileName).setUri("htmlid#"+URI).build();
		List<Runnable> results = interact.getPossibleInteractions("navigateTo", obj, Runnable.class);
		if (results.size() == 0) {
			return;
		}
		results.get(0).run();
	}

	class PivotMenuItem extends SallyMenuItem {

		String fileName;
		SallyInteraction sallyInteraction;
		List<String> ids;
		Long parentProcessID;

		public PivotMenuItem(String frame, String service, String explanation, String fileName, SallyInteraction sallyInteraction, List<String> ids, Long parentProcessID) {
			super(frame, service, explanation);
			this.fileName = fileName;
			this.sallyInteraction = sallyInteraction;
			this.ids = ids;
			this.parentProcessID = parentProcessID;
		}

		@Override
		public void run() {
			Long callbackid = callbacks.registerCallback(new IMessageCallback() {

				@Override
				public void onMessage(AbstractMessage m) {
					navigateTo(sallyInteraction, fileName, (((HTMLSelectPart)m).getId()));
				}
			});

			HashMap<String, Object>  input = new  HashMap<String, Object>();

			List<String> objids = new ArrayList<String>();
			for (String uri : ids) {
				objids.add(uri.substring(7));
			}
			input.put("ObjectIDs", objids);
			input.put("CallbackID", Long.toString(callbackid));
			ProcessInstance pi =wm.prepareProcess(parentProcessID, "Sally.sketch_navigation", input);
			pi.setProcessVarialbe("ServiceURL", "http://localhost:8181/sally/html/navigate?id="+pi.getId());
			wm.startProcess(pi);					
		}
	}

	@SallyService
	public void getRealizations(final SoftwareObject so, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final HashMap<String, List<String>> realizations = getObjectReferences(so, getObjectImplementations);
		final Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);

		int resultCount = realizations.keySet().size();
		if (resultCount == 0)
			return;
		if (resultCount == 1) {
			String fileName = realizations.keySet().iterator().next();
			acceptor.acceptResult(new PivotMenuItem("Instantiations", "In "+fileName +" ("+realizations.get(fileName).size()+")", "", fileName, context.getCurrentInteraction(), realizations.get(fileName), parentProcessInstanceID));
		} else {
			for (String fileName : realizations.keySet()) {
				acceptor.acceptResult(new PivotMenuItem("Variations ", "In "+fileName +" ("+realizations.get(fileName).size()+")", "", fileName, context.getCurrentInteraction(), realizations.get(fileName), parentProcessInstanceID));
			}
		}
	}

	@SallyService
	public void getRequirements(final SoftwareObject so, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final HashMap<String, List<String>> realizations = getObjectReferences(so, getObjectRequirements);
		final Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);

		int resultCount = realizations.keySet().size();
		if (resultCount == 0)
			return;
		if (resultCount == 1) {
			String fileName = realizations.keySet().iterator().next();
			acceptor.acceptResult(new PivotMenuItem("Requirements", "In "+fileName +" ("+realizations.get(fileName).size()+")", "", fileName, context.getCurrentInteraction(), realizations.get(fileName), parentProcessInstanceID));
		} else {
			for (String fileName : realizations.keySet()) {
				acceptor.acceptResult(new PivotMenuItem("Requirements", "In "+fileName +" ("+realizations.get(fileName).size()+")", "", fileName, context.getCurrentInteraction(), realizations.get(fileName), parentProcessInstanceID));
			}
		}
	}

	public void addRelation(String KU, SoftwareObject from,  Property prop, SoftwareObject to) {
		Resource fromRes = addSoftwareObjectToKU(KU, from);
		Resource toRes = addSoftwareObjectToKU(KU, to);
		model.add(fromRes, prop, toRes);
		saveFile();
	}

	SoftwareObject pivotObj;
	String pivotKU;

	@SallyService
	public void planetaryServices(final SoftwareObject soURI, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		acceptor.acceptResult(new SallyMenuItem("- ScrBall4 -", "as" , "") {
			public void run() {
			}
		});
		
		String [] fk = {"Select for refinement (edit)", "Refines Screw Ball ScrBall2 from S1-Req.tex", "Refined to Screw Ball ScrBall6 in S6-embodiment.iam", "Design Variants"};
		for (String f : fk) {
			acceptor.acceptResult(new SallyMenuItem("VDI2221 Design Flow", f , "") {
				public void run() {
				}
			});
		}

		if (pivotKU != null && pivotObj != null) {
			acceptor.acceptResult(new SallyMenuItem(pivotKU, "Is realization of pivot object", "") {
				public void run() {
					addRelation(pivotKU, pivotObj, Pivot.isRealized, soURI);
				}
			});
		}



		for (final String ku : getKnowledgeUnits()) {
			acceptor.acceptResult(new SallyMenuItem(ku, "Add to knowledge unit", "") {
				public void run() {
					addSoftwareObjectToKU(ku, soURI);
				}
			});

			acceptor.acceptResult(new SallyMenuItem(ku, "Set pivot object", "") {
				public void run() {
					pivotObj = soURI;
					pivotKU = ku;
				}
			});
		}

		acceptor.acceptResult(new SallyMenuItem("Knowledge Units", "Add object to new knowledge unit", "") {
			public void run() {
				createKnowledgeUnit("Noname");
			}
		});
	}	

	private String loadSparql(String file) {
		try {
			InputStream is = getClass().getResourceAsStream(file);
			if (is == null)
				return null;
			StringWriter writer = new StringWriter();
			IOUtils.copy(is, writer);
			return writer.toString();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}
}
